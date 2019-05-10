package mlang.core

import mlang.name._

import scala.collection.mutable

sealed trait PatternExtractException extends CoreException

object PatternExtractException {
  case class MakeWrongSize() extends PatternExtractException
  case class MakeIsNotRecordType() extends PatternExtractException
  case class ConstructUnknownName() extends PatternExtractException
  case class ConstructWrongSize() extends PatternExtractException
  case class ConstructNotSumType() extends PatternExtractException
}

import Value._

object Helpers {

}

import Helpers._
sealed trait Value {

  // TODO how does it interact with recursive references?
  def restrict(lv: DimensionPair): Value = this match {
    case u: Universe => u
    case Function(domain, codomain) =>
      Function(domain.restrict(lv), codomain.restrict(lv))
    case Record(level, nodes) =>
      Record(level, nodes.map(n => RecordNode(n.name, n.dependencies, n.closure.restrict(lv))))
    case Make(values) =>
      Make(values.map(_.restrict(lv)))
    case Construct(name, vs) =>
      Construct(name, vs.map(_.restrict(lv)))
    case Sum(level, constructors) =>
      Sum(level, constructors.map(n => Constructor(n.name, n.parameters, n.nodes.map(_.restrict(lv)))))
    case Lambda(closure) =>
      Lambda(closure.restrict(lv))
    case PatternLambda(id, typ, cases) =>
      PatternLambda(id, typ.restrict(lv), cases.map(a => Case(a.pattern, a.closure.restrict(lv))))
    case PathType(typ, left, right) =>
      PathType(typ.restrict(lv), left.restrict(lv), right.restrict(lv))
    case PathLambda(body) =>
      PathLambda(body.restrict(lv))
    case App(lambda, argument) =>
      App(lambda.restrict(lv), argument.restrict(lv))
    case Coe(direction, tp, base) =>
      Coe(direction.restrict(lv), tp.restrict(lv), base.restrict(lv))
    case Hcom(direction, tp, base, faces) =>
      Hcom(direction.restrict(lv), tp.restrict(lv), base.restrict(lv), faces.map(n => Face(n.restriction.restrict(lv), n.body.restrict(lv))))
    case Com(direction, tp, base, faces) =>
      Com(direction.restrict(lv), tp.restrict(lv), base.restrict(lv), faces.map(n => Face(n.restriction.restrict(lv), n.body.restrict(lv))))
    case Maker(value, field) =>
      Maker(value.restrict(lv), field)
    case Projection(make, field) =>
      Projection(make.restrict(lv), field)
    case PatternStuck(lambda, stuck) =>
      PatternStuck(lambda.restrict(lv).asInstanceOf[PatternLambda], stuck.restrict(lv))
    case Let(items, order, body) =>
      Let(items.map(_.restrict(lv)), order, body.restrict(lv))
    case PathApp(left, stuck) =>
      PathApp(left.restrict(lv), stuck.restrict(lv))
    case Generic(id, o) =>
      Generic(id, if (o != null) o.restrict(lv) else null) // some parameter in reify has null types
    case Restricted(a, faces) =>
      Restricted(a, lv +: faces)
    case o: Reference =>
      Restricted(o, Seq(lv))
  }


  final override def equals(obj: Any): Boolean = {
    throw new IllegalArgumentException("Values don't have equal. Either call eq or do conversion checking")
  }

  private var _whnf: Value = _
  private var _from: Value = _




  def wrap(a: Value, map: Value => Value): Value = {
    val w = a.whnf
    if (w.eq(a)) {
      this
    } else {
      map(a)
    }
  }


  // it asserts that if one value cannot be reduced more, it will be eq the original
  def whnf: Value = {
    if (_whnf == null) {
      def eqFaces(f1: Seq[Face], f2: Seq[Face]): Boolean = f1.eq(f2) || (f1.size == f2.size && f1.zip(f2).forall(p => {
        p._1.restriction == p._2.restriction && p._1.body.eq(p._2.body)
      }))
      _whnf = this match {
        case a: HeadCanonical =>
          a
        case r: Reference =>
          r.value.whnf
        case o: Generic =>
          o
        case Maker(r, i) =>
          r.whnf match {
            case s: Sum => s.constructors(i).maker
            case r: Record =>
              assert(i == -1)
              r.maker
            case _ => logicError() // because we don't accept anoymouns maker expression
          }
        case Let(_, _, body) =>
          body.whnf
        case App(lambda, argument) =>
          lambda.whnf.app(argument, whn) match {
            case App(l2, a2) if lambda.eq(l2) && a2.eq(argument) => this
            case a => a
          }
        case PatternStuck(lambda, stuck) =>
          lambda.app(stuck.whnf, whn) match {
            case PatternStuck(l2, s2) if lambda.eq(l2) && stuck.eq(s2) => this
            case a => a
          }
        case Projection(make, field) =>
          make.whnf.project(field, whn) match {
            case Projection(m2, f2) if make.eq(m2) && field == f2 => this
            case a => a
          }
        case PathApp(left, stuck) =>
          left.whnf.papp(stuck, whn) match {
            case PathApp(l2, s2) if left.eq(l2) && stuck == s2 => this
            case a => a
          }
        case Coe(direction, tp, base) =>
          // kan ops case analysis on tp, so they perform their own whnf
          base.coe(direction, tp, whn) match {
            case Coe(d2, t2, b2) if d2 ==direction && t2.eq(tp) && base.eq(b2) => this
            case a => a
          }
        case Hcom(direction, tp, base, faces) =>
          base.hcom(direction, tp, faces, whn) match {
            case Hcom(d2, t2, b2, f2) if direction == d2 && tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
            case a => a
          }
        case Com(direction, tp, base, faces) =>
          base.com(direction, tp, faces, whn) match {
            case Com(d2, t2, b2, f2) if direction == d2 && tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
            case a => a
          }
        case Restricted(a, restriction) =>
          restriction.foldLeft(a.whnf) { (v, r) =>
            v.restrict(r).whnf
          }
      }
      if (!_whnf.eq(this)) _whnf._from = this
      _whnf._whnf = _whnf
    }
    _whnf
  }



  // also used to decide how
  def app(v: Value, returns: Value => Value = id): Value = this match {
    case Lambda(closure) =>
      returns(closure(v))
    case p@PatternLambda(_, _, cases) =>
      // using first match is even ok for overlapping ones
      var res: Value = null
      var cs = cases
      while (cs.nonEmpty && res == null) {
        res = cs.head.tryApp(v).orNull
        cs = cs.tail
      }
      if (res != null) {
        returns(res)
      } else {
        PatternStuck(p, v)
      }
    case _ =>
      App(this, v)
  }


  private def coe(pair: DimensionPair, typ: AbsClosure, returns: Value => Value = id): Value =
    if (pair.isTrue) { // just to base
      returns(this)
    } else {
      typ(Dimension.Generic(vdgen())).whnf match {
        case Function(_, _) =>
          def func(a: Value): Function = a.whnf match {
            case f@Function(_, _) => f
            case _ => logicError()
          }
          returns(Lambda(Value.Closure(a => {
            val a_ = Coe(pair.reverse, typ.map(a => func(a).domain), a)
            val app_ = App(this, a_)
            Coe(pair,
              typ.mapd((f, d) => func(f).codomain(Coe(DimensionPair(pair.to, d), typ.map(a => func(a).domain), a))),
              app_)
          })))
        case Record(_, ns) =>
          if (ns.isEmpty) {
            returns(this)
          } else {
            def recor(a: Value): Record = a.whnf match {
              case f@Record(_, _) => f
              case _ => logicError()
            }
            val closures = mutable.ArrayBuffer[AbsClosure]()
            for (i <- ns.indices) {
              closures.append(
                AbsClosure(dim => {
                  if (ns(i).dependencies.isEmpty) {
                    Coe(
                      DimensionPair(pair.from, dim),
                      typ.map(ror => recor(ror).nodes(i).closure()),
                      Projection(this, i)
                    )
                  } else {
                    Coe(
                      DimensionPair(pair.from, dim),
                      typ.mapd((ror, d) => recor(ror).nodes(i).closure(ns(i).dependencies.map(j => closures(j)(d)))),
                      Projection(this, i)
                    )
                  }
                })
              )
            }
            returns(Make(closures.map(_.apply(pair.to))))
          }
        case PathType(_, _, _) =>
          def pah(a: Value): PathType = a.whnf match {
            case f: PathType => f
            case _ => logicError()
          }
          returns(PathLambda(AbsClosure(dim => {
            Com(
              pair,
              typ.map(a => pah(a).typ(dim)),
              PathApp(this, dim),
              Seq(
                { val dp = DimensionPair(dim, Dimension.True); Face(dp, typ.map(a => pah(a).right.restrict(dp))) },
                { val dp = DimensionPair(dim, Dimension.False); Face(dp, typ.map(a => pah(a).left.restrict(dp))) }
              ))
          })))
        case Sum(l, c) =>
          ???
        case _ =>
          Coe(pair, typ, this)
      }
    }

  private def com(pair: DimensionPair, typ: AbsClosure, restriction0: Seq[Face], returns: Value => Value = id): Value = {
    // do we need to implement the extra shortcuts?
    returns(Hcom(
      pair,
      typ(pair.to),
      Coe(pair, typ, this),
      restriction0.map(n => Face(n.restriction, n.body.mapd((j, d) => Coe(DimensionPair(d, pair.to), typ, j))))))
  }

  private def hcom(pair: DimensionPair, typ: Value, restriction0: Seq[Face], returns: Value => Value = id): Value = {
    val rs0 = restriction0.filter(!_.restriction.isFalse)
    val rs = if (rs0.size == restriction0.size) restriction0 else rs0
    if (pair.isTrue) {
      returns(this)
    } else {
      rs.find(a => a.restriction.from == a.restriction.to) match { // always true face
        case Some(n) =>
          returns(n.body(pair.to))
        case None =>
          typ.whnf match {
            case Function(_, codomain) => returns(Lambda(Value.Closure(a =>
              Hcom(pair, codomain(a), App(this, a), rs.map(n => Face(n.restriction, n.body.map(j => App(j, a)))))
            )))
            case Record(_, ns) =>
              if (ns.isEmpty) {
                returns(this)
              } else {
                val closures = mutable.ArrayBuffer[AbsClosure]()
                for (i <- ns.indices) {
                  closures.append(
                    AbsClosure(dim => {
                      if (ns(i).dependencies.isEmpty) {
                        Hcom(
                          DimensionPair(pair.from, dim),
                          ns(i).closure(),
                          Projection(this, i),
                          rs.map(n => Face(n.restriction, n.body.map(j => Projection(j, i))))
                        )
                      } else {
                        Com(
                          DimensionPair(pair.from, dim),
                          AbsClosure(k => ns(i).closure(ns(i).dependencies.map(j => closures(j)(k)))),
                          Projection(this, 0),
                          rs.map(n => Face(n.restriction, n.body.map(j => Projection(j, i))))
                        )
                      }
                    })
                  )
                }
                returns(Make(closures.map(_.apply(pair.to))))
              }
            case PathType(ty, left, right) =>
              returns(PathLambda(AbsClosure(dim => {
                Hcom(
                  pair,
                  ty(dim),
                  PathApp(this, dim),
                  Seq(
                    { val dp = DimensionPair(dim, Dimension.True); Face(dp, AbsClosure(right.restrict(dp))) },
                    { val dp = DimensionPair(dim, Dimension.False); Face(dp, AbsClosure(left.restrict(dp))) },
                  ) ++ rs.map(n => Face(n.restriction, n.body.map(j => PathApp(j, dim)))))
              })))
            case Sum(l, c) =>
              ???
            case _ =>
              Hcom(pair, typ, this, rs)
          }
      }
    }
  }

  def papp(d: Dimension, returns: Value => Value = id): Value = this match {
    case PathLambda(c) =>
      returns(c(d))
    case a =>
      def constantCase(isOne: Boolean) = {
        infer(a).whnf match {
          case PathType(_, left, right) =>
            returns(if (isOne) right else left)
          case _ => logicError()
        }
      }
      d match {
        case Dimension.True =>
          constantCase(true)
        case Dimension.False =>
          constantCase(false)
        case _: Dimension.Generic =>
          PathApp(this, d)
      }
  }


  def makerType(i: Int): Value = this.whnf match {
    case s: Sum => s.constructors(i).makerType
    case v: Record => v.makerType
    case _ => logicError()
  }

  def project(name: Int, returns: Value => Value = id): Value = {
    this match {
      case Make(vs) => returns(vs(name))
      case _ => Projection(this, name)
    }
  }
}


object Value {

  implicit class MultiClosure(private val func: Seq[Value]=> Value) extends AnyVal {
    def eq(b: MultiClosure) = func.eq(b.func)
    def apply() = func(Seq.empty)
    def apply(seq: Seq[Value]): Value = func(seq)
    def restrict(lv: DimensionPair): MultiClosure = Value.MultiClosure(v => this(v).restrict(lv))
  }

  implicit class Closure(private val func: Value => Value) extends AnyVal {
    def eq(b: Closure) = func.eq(b.func)
    def apply(seq: Value): Value = func(seq)
    def restrict(lv: DimensionPair): Closure = Value.Closure(v => this(v).restrict(lv))
  }

  object Closure {
    def apply(a: Value): Closure = Closure(_ => a)
  }

  object AbsClosure {
    def apply(a: Value): AbsClosure = AbsClosure(_ => a)
  }

  implicit class AbsClosure(private val func: Dimension => Value) extends AnyVal {
    def eq(b: AbsClosure) = func.eq(b.func)
    def apply(seq: Dimension): Value = func(seq)
    def restrict(lv: DimensionPair): AbsClosure = Value.AbsClosure(v => this(v).restrict(lv))
    def mapd(a: (Value, Dimension) => Value): AbsClosure = AbsClosure(d => a(this(d), d))
    def map(a: Value => Value): AbsClosure = AbsClosure(d => a(this(d)))
  }


  case class DimensionPair(from: Dimension, to: Dimension) {
    def restrict(lv: DimensionPair): DimensionPair = DimensionPair(from.restrict(lv), to.restrict(lv))

    def reverse: DimensionPair = DimensionPair(to, from)

    def isFalse: Boolean = (from == Dimension.False && to == Dimension.True) || (from == Dimension.True && to == Dimension.False)

    def isTrue: Boolean = from == to

    def sorted: DimensionPair = if ((to max from) == to) this else DimensionPair(to, from)
  }

  sealed trait Dimension extends {
    def matches(id: Long): Boolean = this match {
      case Dimension.Generic(iid) => iid == id
      case _ => false
    }

    def isConstant: Boolean = this match {
      case Dimension.Generic(_) => false
      case _ => true
    }

    def min(t: Dimension): Dimension = if ((this max t) == t) this else t

    def max(t: Dimension): Dimension = (this, t) match {
      case (Dimension.Generic(a), Dimension.Generic(b)) =>
        Dimension.Generic(a max b)
      case (c, _: Dimension.Generic) =>
        c
      case (_: Dimension.Generic, c) =>
        c
      case (a, b) =>
        assert(a == b, "You should trim false faces")
        a
    }

    def restrict(pair: DimensionPair): Dimension = this match {
      case Dimension.Generic(id) =>
        if (pair.from.matches(id) || pair.to.matches(id)) {
          pair.from max pair.to
        } else {
          this
        }
      case _ => this
    }
  }

  object Dimension {
    case class Generic(id: Long) extends Dimension

    object True extends Dimension
    object False extends Dimension
  }

  type StuckPos = Value
  // these serve the purpose of recovering syntax
  sealed trait Syntaxial extends Value
  sealed trait Whnf extends Value
  sealed trait HeadCanonical extends Whnf
  sealed trait Stuck extends Whnf

  case class Reference(value: Value) extends Syntaxial
  case class Generic(id: Long, typ: Value) extends Stuck

  case class Universe(level: Int) extends HeadCanonical

  object Universe {
    def up(i: Int) = Universe(i) // type : type for now
  }

  case class Function(domain: Value, codomain: Closure) extends HeadCanonical
  case class App(lambda: StuckPos, argument: Value) extends Stuck


  case class RecordNode(name: Name, dependencies: Seq[Int], closure: MultiClosure)

  // TODO should have a field: recursive, and it must be recursive, the will not be able to calculus
  case class Record(level: Int, nodes: Seq[RecordNode]) extends HeadCanonical {
    assert(nodes.isEmpty || nodes.head.dependencies.isEmpty)

    private def rthis(): Value = Reference(this)

    lazy val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[RecordNode]): Value = {
        remaining match {
          case Seq() => Make(known)
          case _ +: tail =>
            Lambda(Closure(p => rec(known :+ p, tail)))
        }
      }
      rec(Seq.empty, nodes)
    }

    lazy val makerType: Value = {
      def rec(known: Seq[Value], remaining: Seq[RecordNode]): Value = {
        remaining match {
          case Seq() => rthis()
          case Seq(head) =>
            Function(head.closure(head.dependencies.map(known)),
              Closure(_ => rthis()))
          case head +: tail =>
            Function(head.closure(head.dependencies.map(known)), Closure(p => {
              rec(known ++ Seq(p), tail)
            }))
        }
      }
      rec(Seq.empty, nodes)
    }
    def projectedType(values: Seq[Value], name: Int): Value = {
      val b = nodes(name)
      b.closure(b.dependencies.map(values))
    }
  }

  case class Face(restriction: DimensionPair, body: AbsClosure)

  case class Restricted(a: Reference, faces: Seq[DimensionPair]) extends Syntaxial

  case class Coe(direction: DimensionPair, tp: AbsClosure, base: Value) extends Stuck

  case class Com(direction: DimensionPair, tp: AbsClosure, base: Value, faces: Seq[Face]) extends Stuck

  case class Hcom(direction: DimensionPair, tp: Value, base: Value, faces: Seq[Face]) extends Stuck

  case class Make(values: Seq[Value]) extends HeadCanonical

  // it cannot actually stuck. it is a syntaxal value
  case class Maker(value: Value, field: Int) extends Syntaxial

  case class Projection(make: StuckPos, field: Int) extends Stuck

  case class Construct(name: Tag, vs: Seq[Value]) extends HeadCanonical
  // TODO sum should have a type, it can be indexed, so a pi type ends with type_i
  // TODO should have a field: recursive, and it must be recursive, also in case of indexed, use Constructor instead of value
  case class Constructor(name: Tag, parameters: Int, nodes: Seq[MultiClosure]) {
    private[Value] var _sum: Sum = _
    private def rthis(): Value = Reference(_sum)

    lazy val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[MultiClosure]): Value = {
        remaining match {
          case Seq() => Construct(name, known)
          case _ +: tail =>
            Lambda(Closure(p => rec(known :+ p, tail)))
        }
      }
      rec(Seq.empty, nodes)
    }

    lazy val makerType: Value = {
      def rec(known: Seq[Value], remaining: Seq[MultiClosure]): Value = {
        remaining match {
          case Seq() => rthis()
          case Seq(head) =>
            Function(head(known), Closure(_ => rthis()))
          case head +: _ +: tail =>
            Function(head(known), Closure(p => {
              rec(known :+ p, tail)
            }))
        }
      }
      rec(Seq.empty, nodes)
    }
  }

  case class Sum(level: Int, constructors: Seq[Constructor]) extends HeadCanonical {
    for (c <- constructors) {
      c._sum = this
    }
  }

  case class Case(pattern: Pattern, closure: MultiClosure) {
    def tryApp(v: Value): Option[Value] = {
      extract(pattern, v).map(a => closure(a))
    }
  }

  /**
    * this lambda is returnsparent on the arguments
    */
  case class Lambda(closure: Closure) extends HeadCanonical

  case class PatternLambda(id: Long, typ: Closure, cases: Seq[Case]) extends HeadCanonical

  case class PatternStuck(lambda: PatternLambda, stuck: StuckPos) extends Stuck

  case class Let(var items: Seq[Value], order: Seq[Int], body: Value) extends Syntaxial


  case class PathType(typ: AbsClosure, left: Value, right: Value) extends HeadCanonical

  case class PathLambda(body: AbsClosure) extends HeadCanonical

  // the left and right BOTH stuck
  case class PathApp(left: StuckPos, dimension: Dimension) extends Stuck

  // these values will not be visible to users! also I guess it is ok to be static, it will not overflow right?
  private val vgen = new LongGen.Negative()
  private val vdgen = new LongGen.Negative()

  def inferLevel(t1: Value): Int = infer(t1) match {
    case Universe(l) => l
    case _ => logicError()
  }

  // only works for values of path type and universe types
  def infer(t1: Value): Value = {
    t1.whnf match {
      case Generic(_, v1) =>
        v1
      case Universe(level) => Universe.up(level)
      case Function(domain, codomain) =>
        (infer(domain), infer(codomain(Generic(vgen(), domain)))) match {
          case (Universe(l1), Universe(l2)) => Universe(l1 max l2)
          case _ => logicError()
        }
      case Record(level, _) =>
        Universe(level)
      case Sum(level, _) =>
        Universe(level)
      case PathType(typ, _, _) =>
        infer(typ.apply(Dimension.Generic(vdgen())))
      case App(l1, a1) =>
        infer(l1).whnf match {
          case Function(_, c) =>
            c(a1)
          case _ => logicError()
        }
      case Projection(m1, f1) =>
        infer(m1).whnf match {
          case rr: Record  => rr.projectedType(rr.nodes.indices.map(n => Projection(m1, n)), f1)
          case _ => logicError()
        }
      case PatternStuck(l1, s1) =>
        l1.typ(s1)
      case PathApp(l1, d1) =>
        infer(l1).whnf match {
          case PathType(typ, _, _) => typ(d1)
          case _ => logicError()
        }
      case _ => logicError()
    }
  }



  def extract(pattern: Pattern, v: Value): Option[Seq[Value]] = {
    val vs = mutable.ArrayBuffer[Value]()
    def rec(pattern: Pattern, v: Value): Boolean = {
      pattern match {
        case Pattern.Atom =>
          vs.append(v)
          true
        case Pattern.Make(names) =>
          v.whnf match {
            case Make(values) =>
              names.zip(values).forall(pair => rec(pair._1, pair._2))
            case _ =>
              false
          }
        case Pattern.Construct(name, pt) =>
          v.whnf match {
            case Construct(n, values) if name == n =>
              pt.zip(values).forall(pair => rec(pair._1, pair._2))
            case _ =>
              false
          }
      }
    }
    if (rec(pattern, v)) {
      Some(vs)
    } else {
      None
    }
  }

  def id(v: Value): Value = v

  def whn (v: Value): Value = v.whnf

}

