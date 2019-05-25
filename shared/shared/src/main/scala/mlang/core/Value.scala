package mlang.core

import mlang.name._
import mlang.utils.{DisjointSet, debug}

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

sealed trait Value {


  def from: Value = if (_from == null) this else _from

  /**
    *
    * HOW DOES restrict interacts with Up
    *
    * these two are translated to calls, not Stuck in eval
    *
    * they act structurally on all syntax, and block on all references (closed, generic, meta)
    *
    * so they block on each other, and we will ensure that the canonical block order is Restrict(Up(XxxReference))
    *
    */
  def restrict(a: Seq[DimensionPair]): Value = a.foldLeft(this) {(t, v) => t.restrict(v) }

  def up(b: Int) : Value = this match {
    case Universe(i) =>
      Universe(i + b)
    case Function(domain, im, codomain) =>
      Function(domain.up(b), im, codomain.up(b))
    case Record(level, inductively, ms, ns, nodes) =>
      Record(level + 1, inductively.map(_.up(b)), ms, ns, ClosureGraph.up(nodes, b))
    case Make(values) =>
      Make(values.map(_.up(b)))
    case Construct(name, vs) =>
      Construct(name, vs.map(_.up(b)))
    case Sum(level, inductively, constructors) =>
      Sum(level + 1, inductively.map(_.up(b)), constructors.map(n => Constructor(n.name, n.ims, ClosureGraph.up(n.nodes, b))))
    case Lambda(closure) =>
      Lambda(closure.up(b))
    case PatternLambda(id, dom, typ, cases) =>
      PatternLambda(id, dom.up(b), typ.up(b), cases.map(a => Case(a.pattern, a.closure.up(b))))
    case PathType(typ, left, right) =>
      PathType(typ.up(b), left.up(b), right.up(b))
    case PathLambda(body) =>
      PathLambda(body.up(b))
    case App(lambda, argument) =>
      App(lambda.up(b), argument.up(b))
    case Coe(direction, tp, base) =>
      Coe(direction, tp.up(b), base.up(b))
    case Hcom(direction, tp, base, faces) =>
      Hcom(direction, tp.up(b), base.up(b), faces.map(n => Face(n.restriction, n.body.up(b))))
    case Com(direction, tp, base, faces) =>
      Com(direction, tp.up(b), base.up(b), faces.map(n => Face(n.restriction, n.body.up(b))))
    case Maker(value, field) =>
      Maker(value.up(b), field)
    case Projection(make, field) =>
      Projection(make.up(b), field)
    case PatternStuck(lambda, stuck) =>
      PatternStuck(lambda.up(b).asInstanceOf[PatternLambda], stuck.up(b))
    case Let(items, body) =>
      Let(items.map(_.up(b)), body.up(b))
    case PathApp(left, stuck) =>
      PathApp(left.up(b), stuck)
    case Restricted(a, faces) =>
      Restricted(a.up(b), faces)
    case Up(c, d) =>
      if (b + d == 0) c
      else Up(c, b + d)
    case g: Generic =>
      Up(g, b)
    case o: Meta =>
      Up(o, b)
    case o: Reference =>
      Up(o, b)
  }

  // TODO how does it interact with recursive references?
  def restrict(lv: DimensionPair): Value =  this match {
    case u: Universe => u
    case Function(domain, im, codomain) =>
      Function(domain.restrict(lv), im, codomain.restrict(lv))
    case Record(level, inductively, ms, ns, nodes) =>
      Record(level, inductively.map(_.restrict(lv)), ms, ns, ClosureGraph.restrict(nodes, lv))
    case Make(values) =>
      Make(values.map(_.restrict(lv)))
    case Construct(name, vs) =>
      Construct(name, vs.map(_.restrict(lv)))
    case Sum(level, inductively, constructors) =>
      Sum(level, inductively.map(_.restrict(lv)), constructors.map(n => Constructor(n.name, n.ims, ClosureGraph.restrict(n.nodes, lv))))
    case Lambda(closure) =>
      Lambda(closure.restrict(lv))
    case PatternLambda(id, dom, typ, cases) =>
      PatternLambda(id, dom.restrict(lv), typ.restrict(lv), cases.map(a => Case(a.pattern, a.closure.restrict(lv))))
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
    case Let(items, body) =>
      Let(items.map(_.restrict(lv)), body.restrict(lv))
    case PathApp(left, stuck) =>
      PathApp(left.restrict(lv), stuck.restrict(lv))
    case Up(a, b) =>
      Restricted(Up(a, b), Seq(lv))
    case Restricted(a, faces) =>
      Restricted(a, lv +: faces)
    case g: Generic =>
      Restricted(g, Seq(lv))
    case o: Reference =>
      Restricted(o, Seq(lv))
    case o: Meta =>
      Restricted(o, Seq(lv))
  }


  final override def equals(obj: Any): Boolean = {
    throw new IllegalArgumentException("Values don't have equal. Either call eq or do conversion checking")
  }

  @cached_mutation private var _from: Value = _
  @cached_mutation private var _whnf: Value = _




  // it asserts that if one value cannot be reduced more, it will be eq the original
  def whnf: Value = {
    if (_whnf == null) {
      // TODO can we sort by restriction first?
      def eqFaces(f1: Seq[Face], f2: Seq[Face]): Boolean = f1.eq(f2) || (f1.size == f2.size && f1.zip(f2).forall(p => {
        p._1.restriction.sameRestrict(p._2.restriction) && p._1.body.eq(p._2.body)
      }))
      val candidate = this match {
        case a: HeadCanonical =>
          a
        case r: Reference =>
          r.value.whnf
        case o: Generic =>
          o
        case m: Meta =>
          m.v match {
            case Meta.Closed(v) => v.whnf
            case _: Meta.Open => m
          }
        case Maker(r, i) =>
          r.whnf match {
            case s: Sum => s.constructors(i).maker
            case r: Record =>
              assert(i == -1)
              r.maker
            case _ => logicError() // because we don't accept anoymouns maker expression
          }
        case Let(_, body) =>
          body.whnf
        case App(lambda, argument) =>
          app(lambda.whnf, argument, _.whnf) match {
            case App(l2, a2) if lambda.eq(l2) && a2.eq(argument) => this
            case a => a
          }
        case PatternStuck(lambda, stuck) =>
          split(lambda, stuck.whnf, _.whnf) match {
            case PatternStuck(l2, s2) if lambda.eq(l2) && stuck.eq(s2) => this
            case a => a
          }
        case Projection(make, field) =>
          project(make.whnf, field, _.whnf) match {
            case Projection(m2, f2) if make.eq(m2) && field == f2 => this
            case a => a
          }
        case PathApp(left, stuck) =>
          // we MUST perform this, because this doesn't care
          papp(left.whnf, stuck) match {
            case PathApp(l2, s2) if left.eq(l2) && stuck == s2 => this
            case a => a.whnf
          }
        case Coe(direction, tp, base) =>
          // kan ops case analysis on tp, so they perform their own whnf
          coe(direction, tp, base, _.whnf) match {
            case Coe(d2, t2, b2) if d2 == direction && t2.eq(tp) && base.eq(b2) => this
            case a => a
          }
        case Hcom(direction, tp, base, faces) =>
          hcom(direction, tp, base, faces, _.whnf) match {
            case Hcom(d2, t2, b2, f2) if direction == d2 && tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
            case a => a
          }
        case Com(direction, tp, base, faces) =>
          com(direction, tp, base, faces, _.whnf) match {
            case Com(d2, t2, b2, f2) if direction == d2 && tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
            case a => a
          }
        case Restricted(a, restriction) =>
          val normalized = DimensionPair.normalizeRestriction(restriction)
          if (normalized.isEmpty) {
            a.whnf
          } else {
            a match {
              case GenericOrOpenMeta(it) => Restricted(it, normalized) // stop case
              case u: Up => u.whnf match {
                case Up(GenericOrOpenMeta(it), b) => Restricted(Up(it, b), normalized) // a up's whnf can only block on generics
                case j => j.restrict(normalized).whnf
              }
              case _ => a.restrict(normalized).whnf
            }
          }
        case Up(a, b) =>
          // a can only be reference
          a match {
            case GenericOrOpenMeta(it) => Up(it, b) // stop case
            case ReferenceTail(v, c) => c.map(_.derefUpSaved(b)).getOrElse(v.up(b)).whnf
          }
      }
      candidate._from = this
      candidate match {
        case Value.OpenMetaHeaded(_) =>
        case _ =>
          // remember for stable values
          _whnf = candidate
          candidate._whnf = candidate
      }
      candidate
    } else {
      _whnf
    }
  }






  def makerType(i: Int): Value = this.whnf match {
    case s: Sum => s.constructors(i).makerType
    case v: Record => v.makerType
    case _ => logicError()
  }
}


object Value {

  type ClosureGraph = Seq[ClosureGraph.Node]
  object ClosureGraph {
    def up(graph: ClosureGraph, uu: Int): ClosureGraph = {
      graph.map {
        case DependentWithMeta(ds, mc, c) => DependentWithMeta(ds, mc, (a, b) => { val t = c(a.map(_.up(-uu)), b.map(_.up(-uu))); (t._1.map(_.up(uu)), t._2.up(uu)) })
        case IndependentWithMeta(ds, ms, typ) => IndependentWithMeta(ds, ms.map(_.up(uu)), typ.up(uu))
        case _ => logicError()
      }
    }

    def restrict(graph: ClosureGraph, lv: DimensionPair): ClosureGraph = {
      graph.map {
        case DependentWithMeta(ds, mc, c) => DependentWithMeta(ds, mc, (a, b) => { val t = c(a, b); (t._1.map(_.restrict(lv)), t._2.restrict(lv)) })
        case IndependentWithMeta(ds, ms, typ) => IndependentWithMeta(ds, ms.map(_.restrict(lv)), typ.restrict(lv))
        case _ => logicError()
      }
    }

    sealed trait Node {
      def dependencies: Seq[Int]
      def independent: Independent = this.asInstanceOf[Independent]
    }

    sealed trait Dependent extends Node {
    }

    sealed trait Independent extends Node {
      val typ: Value
    }

    private sealed trait Valued extends Independent {
      val value: Value
    }

    private case class DependentWithMeta(dependencies: Seq[Int], metaCount: Int, closure: (Seq[Value], Seq[Value]) => (Seq[Value], Value)) extends Dependent

    private case class IndependentWithMeta(dependencies: Seq[Int], metas: Seq[Value], typ: Value) extends Independent {
    }

    private case class PrivateValuedWithMeta(dependencies: Seq[Int], metas: Seq[Value], typ: Value, value: Value) extends Valued {
    }

    def createTemp(nodes: Seq[(Seq[Int], Seq[Value] => Value)]): ClosureGraph = {
      createMetaAnnotated(nodes.map(a => (a._1, 0, (_: Seq[Value], vs: Seq[Value]) => (Seq.empty[Value], a._2(vs)))))
    }

    def createMetaAnnotated(nodes: Seq[(Seq[Int], Int, (Seq[Value], Seq[Value]) => (Seq[Value], Value))]): ClosureGraph = {
      nodes.map(a => if (a._1.isEmpty) {
        val t = a._3(Seq.empty, Seq.empty)
        IndependentWithMeta(a._1, t._1, t._2)
      } else {
        DependentWithMeta(a._1, a._2, a._3)
      })
    }

    def get(nodes: ClosureGraph, name: Int, values: Int => Value): Value = {
      var i = 0
      var g = nodes
      while (i < name) {
        g = ClosureGraph.reduce(g, i, values(i))
        i += 1
      }
      g(name).independent.typ
    }


    def reduce(from: ClosureGraph, i: Int, a: Value): ClosureGraph = {
      from(i) match {
        case IndependentWithMeta(ds, mss, typ) =>
          val ns = PrivateValuedWithMeta(ds, mss, typ, a)
          val mms: Seq[Value] = from.flatMap {
            case DependentWithMeta(_, ms, _) => (0 until ms).map(_ => null: Value)
            case IndependentWithMeta(_, ms, _) => ms
            case PrivateValuedWithMeta(_, ms, _, _) => ms
          }
          val vs = from.indices.map(j => if (j == i) a else from(j) match {
            case PrivateValuedWithMeta(_, _, _, v) => v
            case _ => null
          })
          from.map {
            case DependentWithMeta(dss, _, c) if dss.forall(j => vs(j) != null) =>
              val t = c(mms, vs)
              IndependentWithMeta(dss, t._1, t._2)
            case k => k
          }.updated(i, ns)
        case _ => logicError()
      }
    }

    def makerAndType(graph: ClosureGraph, ims: Seq[Boolean], vc: Seq[Value] => Value, tc: Value): (Value, Value) = {
      def rmake(known: Seq[Value]): Value = {
        val size = graph.size - known.size
        size match {
          case 0 => vc(known)
          case _ => Lambda(Closure(p => rmake(known :+ p)))
        }
      }
      def rtyp(index: Int, graph: Seq[ClosureGraph.Node]): Value = {
        val size = graph.size - index
        size match {
          case 0 => tc
          case _ =>
            Function(graph(index).independent.typ, ims(index), Closure(p => {
              val ng = reduce(graph, index, p)
              rtyp(index + 1, ng)
          }))
        }
      }
      val mv = rmake(Seq.empty)
      val mt = rtyp(0, graph)
      (mv, mt)
    }
  }

  def app(lambda: Value, argument: Value, returns: Value => Value = id): Value = {
    lambda match {
      case Lambda(closure) =>
        returns(closure(argument))
      case p : PatternLambda =>
        split(p, argument, returns)
      case _ =>
        App(lambda, argument)
    }
  }

  def split(l: PatternLambda, argument: Value, returns: Value => Value = id): Value = {
    // using first match is even ok for overlapping ones
    var res: Value = null
    var cs = l.cases
    while (cs.nonEmpty && res == null) {
      res = cs.head.tryApp(argument).orNull
      cs = cs.tail
    }
    if (res != null) {
      returns(res)
    } else {
      PatternStuck(l, argument)
    }
  }


  def project(v: Value, name: Int, returns: Value => Value = id): Value = {
    v match {
      case Make(vs) => returns(vs(name))
      case _ => Projection(v, name)
    }
  }

  def papp(l: Value, d: Dimension, returns: Value => Value = id): Value = l match {
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
          PathApp(l, d)
      }
  }

  def id(v: Value) = v

  private def coe(pair: DimensionPair, typ: AbsClosure, base: Value, returns: Value => Value = id): Value =
    if (pair.isTrue) { // just to base
      returns(base)
    } else {
      typ(Dimension.Generic(vdgen())).whnf match {
        case Function(_, _, _) =>
          def func(a: Value): Function = a.whnf match {
            case f: Function => f
            case _ => logicError()
          }
          returns(Lambda(Value.Closure(a => {
            val a_ = Coe(pair.reverse, typ.map(a => func(a).domain), a)
            val app_ = App(base, a_)
            Coe(pair,
              typ.mapd((f, d) => func(f).codomain(Coe(DimensionPair(pair.to, d), typ.map(a => func(a).domain), a))),
              app_)
          })))
        case r: Record =>
          val graph = r.nodes
          if (graph.isEmpty) {
            returns(base)
          } else {
            def recor(a: Value): Record = a.whnf match {
              case f: Record => f
              case _ => logicError()
            }
            val closures = mutable.ArrayBuffer[AbsClosure]()
            for (i <- graph.indices) {
              closures.append(
                AbsClosure(dim => {
                  graph(i) match {
                    case _: ClosureGraph.Independent =>
                      Coe(
                        DimensionPair(pair.from, dim),
                        typ.map(ror => recor(ror).nodes(i).independent.typ),
                        Projection(base, i)
                      )
                    case _: ClosureGraph.Dependent =>
                      Coe(
                        DimensionPair(pair.from, dim),
                        typ.mapd((ror, d) => { ClosureGraph.get(recor(ror).nodes, i, j => closures(j)(d)) }),
                        Projection(base, i)
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
              PathApp(base, dim),
              Seq(
                { val dp = DimensionPair(dim, Dimension.True); Face(dp, typ.map(a => pah(a).right.restrict(dp))) },
                { val dp = DimensionPair(dim, Dimension.False); Face(dp, typ.map(a => pah(a).left.restrict(dp))) }
              ))
          })))
        case Sum(l, inductively, c) =>
          ???
        case _ =>
          Coe(pair, typ, base)
      }
    }

  private def com(pair: DimensionPair, typ: AbsClosure, base: Value, restriction0: Seq[Face], returns: Value => Value = id): Value = {
    // do we need to implement the extra shortcuts?
    returns(Hcom(
      pair,
      typ(pair.to),
      Coe(pair, typ, base),
      restriction0.map(n => Face(n.restriction, n.body.mapd((j, d) => Coe(DimensionPair(d, pair.to), typ, j))))))
  }

  private def hcom(pair: DimensionPair, typ: Value, base: Value, restriction0: Seq[Face], returns: Value => Value = id): Value = {
    val rs0 = restriction0.filter(!_.restriction.isFalse)
    val rs = if (rs0.size == restriction0.size) restriction0 else rs0
    if (pair.isTrue) {
      returns(base)
    } else {
      rs.find(a => a.restriction.isTrue) match { // always true face
        case Some(n) =>
          returns(n.body(pair.to))
        case None =>
          typ.whnf match {
            case Function(_, _, codomain) => returns(Lambda(Value.Closure(a =>
              Hcom(pair, codomain(a), App(base, a), rs.map(n => Face(n.restriction, n.body.map(j => App(j, a)))))
            )))
            case r: Record =>
              val graph = r.nodes
              if (graph.isEmpty) {
                returns(base)
              } else {
                def recor(a: Value): Record = a.whnf match {
                  case f: Record => f
                  case _ => logicError()
                }
                val closures = mutable.ArrayBuffer[AbsClosure]()
                for (i <- graph.indices) {
                  closures.append(
                    AbsClosure(dim => {
                      graph(i) match {
                        case in: ClosureGraph.Independent =>
                          Hcom(
                            DimensionPair(pair.from, dim),
                            in.typ,
                            Projection(base, i),
                            rs.map(n => Face(n.restriction, n.body.map(j => Projection(j, i))))
                          )
                        case _: ClosureGraph.Dependent =>
                          Com(
                            DimensionPair(pair.from, dim),
                            AbsClosure(k => ClosureGraph.get(graph, i, j => closures(j)(k))),
                            Projection(base, 0),
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
                  PathApp(base, dim),
                  Seq(
                    { val dp = DimensionPair(dim, Dimension.True); Face(dp, AbsClosure(right.restrict(dp))) },
                    { val dp = DimensionPair(dim, Dimension.False); Face(dp, AbsClosure(left.restrict(dp))) },
                  ) ++ rs.map(n => Face(n.restriction, n.body.map(j => PathApp(j, dim)))))
              })))
            case Sum(l, inductively, c) =>
              ???
            case _ =>
              Hcom(pair, typ, base, rs)
          }
      }
    }
  }



  implicit class MultiClosure(private val func: Seq[Value] => Value) extends AnyVal {
    def eq(b: MultiClosure): Boolean = func.eq(b.func)
    def apply() = func(Seq.empty)
    def apply(seq: Seq[Value]): Value = func(seq)
    def restrict(lv: DimensionPair): MultiClosure = Value.MultiClosure(v => this(v).restrict(lv))
    def up(b: Int): Value.MultiClosure = Value.MultiClosure(v => this(v.map(_.up(-b))).up(b))
  }

  implicit class Closure(private val func: Value => Value) extends AnyVal {

    def eq(b: Closure): Boolean = func.eq(b.func)
    def apply(seq: Value): Value = func(seq)
    def restrict(lv: DimensionPair): Closure = Value.Closure(v => this(v).restrict(lv))
    def up(b: Int): Value.Closure = Value.Closure(v => this(v.up(-b)).up(b))
  }

  object Closure {
    def apply(a: Value): Closure = Closure(_ => a)
  }

  object AbsClosure {
    def apply(a: Value): AbsClosure = AbsClosure(_ => a)
    type StuckPos = AbsClosure
  }

  implicit class AbsClosure(private val func: Dimension => Value) extends AnyVal {
    def eq(b: AbsClosure): Boolean = func.eq(b.func)
    def apply(seq: Dimension): Value = func(seq)
    def restrict(lv: DimensionPair): AbsClosure = Value.AbsClosure(v => this(v).restrict(lv))
    def up(b: Int): Value.AbsClosure = Value.AbsClosure(v => this(v).up(b))
    def mapd(a: (Value, Dimension) => Value): AbsClosure = AbsClosure(d => a(this(d), d))
    def map(a: Value => Value): AbsClosure = AbsClosure(d => a(this(d)))
  }

  object DimensionPair {
    def checkValidRestrictions(ds0: Seq[DimensionPair]): Boolean = {
      // TODO this is an extension for validity now, we don't make a difference between i=j and j=i
      val ds = ds0.map(_.sorted)
      ds.exists(a => a.isTrue) || ds.flatMap(r => ds.map(d => (r, d))).exists(p => {
        p._1.from == p._2.from && !p._1.from.isConstant &&
            p._1.to.isConstant && p._2.to.isConstant && p._1.to != p._2.to
      })
    }

    def normalizeRestriction(pairs: Seq[DimensionPair]): Seq[DimensionPair] = {
      val a = DisjointSet[Dimension]()
      for (p <- pairs) {
        if (!a.contains(p.from)) a += p.from
        if (!a.contains(p.to)) a += p.to
        a.union(p.from, p.to)
      }
      val seq = a.sets.map(_.toSeq).filter(_.size <= 1).toSeq
          .map(_.sortWith((a, b) => (a max b) == b))
          .sortWith((a, b) => (a.last max b.last) == b.last)
      if (debug.enabled) assert(!seq.exists(_.endsWith(Seq(Dimension.False, Dimension.True))))
      seq.flatMap(a => a.dropRight(1).map(b => DimensionPair(b, a.last)))
    }

    def sameRestrict(p: Seq[DimensionPair], r: Seq[DimensionPair]): Boolean = {
      normalizeRestriction(p) == normalizeRestriction(r)
    }
  }

  case class DimensionPair(from: Dimension, to: Dimension) {
    def restrict(a: DimensionPair) = DimensionPair(from.restrict(a), to.restrict(a))

    def sameRestrict(p: DimensionPair): Boolean = this.sorted == p.sorted

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
      case (Dimension.True, _) =>
        Dimension.True
      case (_, Dimension.True) =>
        Dimension.True
      case _ =>
        Dimension.False
    }

    def restrict(seq: Seq[DimensionPair]): Dimension = seq.foldLeft(this) { (t, v) => t.restrict(v) }

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


  object Meta {
    sealed trait State

    case class Closed(v: Value) extends State
    case class Open(id: Long, typ: Value) extends State
  }
  case class Meta(@polarized_mutation var v: Meta.State) extends Syntaxial {
    def solved: Value = v.asInstanceOf[Meta.Closed].v
    def isSolved: Boolean = v.isInstanceOf[Meta.Closed]
  }

  case class Reference(@lateinit private var value000: Value) extends Syntaxial {
    @cached_mutation private val _ups = mutable.ArrayBuffer.empty[Value]
    def value: Value =  value000
    def value_=(v: Value): Unit = {
      _ups.clear()
      value000 = v
    }

    def derefUpSaved(b: Int): Value = {
      if (b < _ups.size && _ups(b) != null) {
        _ups(b)
      } else {
        val v = value.up(b)
        while (b >= _ups.size) _ups.append(null)
        _ups.update(b, v)
        v
      }
    }

    override def toString: String = "Reference"
  }

  object ReferenceTail {
    def rec(a: Value, ref: Option[Reference]): Option[(Value, Option[Reference])] = a match {
      case Meta(Meta.Closed(v)) => rec(v, ref)
      case r@Reference(t) => rec(t, Some(r))
      case els => Some((els, ref))
    }
    def unapply(a: Value): Option[(Value, Option[Reference])] = rec(a, None)
  }
  object GenericOrOpenMeta {
    def unapply(a: Value): Option[Value] = a match {
      case g: Generic => Some(g)
      case Meta(m: Meta.Open) => Some(a)
      case _ => None
    }
  }

  case class Generic(id: Long, @lateinit var typ: Value) extends Stuck

  case class Universe(level: Int) extends HeadCanonical {
    assert(level >= 0)
  }

  object Universe {
    def suc(i: Int) = Universe(i + 1)
  }

  case class Up(term: Value, level: Int) extends Syntaxial

  case class Function(domain: Value, impict: Boolean, codomain: Closure) extends HeadCanonical
  case class App(lambda: StuckPos, argument: Value) extends Stuck

  case class Inductively(id: Long) {
    def up(b: Int): Inductively = this
    def restrict(lv: DimensionPair): Inductively = this
  }

  case class Record(
      level: Int,
      inductively: Option[Inductively],
      names: Seq[Name],
      ims: Seq[Boolean],
      nodes: ClosureGraph) extends HeadCanonical {
    assert(names.size == nodes.size)

    private def rthis(): Value = Reference(this)

    private lazy val makerAndType: (Value, Value) = ClosureGraph.makerAndType(nodes, ims, vs => Make(vs), rthis())
    lazy val maker: Value = makerAndType._1
    lazy val makerType: Value = makerAndType._2

    def projectedType(values: Seq[Value], name: Int): Value = {
      ClosureGraph.get(nodes, name, values)
    }
  }

  case class Face(restriction: DimensionPair, body: AbsClosure)

  case class Restricted(a: Value, faces: Seq[DimensionPair]) extends Syntaxial

  case class Coe(direction: DimensionPair, tp: AbsClosure.StuckPos, base: Value) extends Stuck

  case class Com(direction: DimensionPair, tp: AbsClosure.StuckPos, base: Value, faces: Seq[Face]) extends Stuck

  case class Hcom(direction: DimensionPair, tp: StuckPos, base: Value, faces: Seq[Face]) extends Stuck

  case class Make(values: Seq[Value]) extends HeadCanonical

  // it cannot actually stuck. it is a syntaxal value
  case class Maker(value: Value, field: Int) extends Syntaxial

  case class Projection(make: StuckPos, field: Int) extends Stuck

  case class Construct(name: Int, vs: Seq[Value]) extends HeadCanonical
  // TODO sum should have a type, it can be indexed, so a pi type ends with type_i
  case class Constructor(name: Name, ims: Seq[Boolean], nodes: ClosureGraph) {
    private[Value] var _sum: Sum = _
    private def rthis(): Value = Reference(_sum)

    private def index = _sum.constructors.indexWhere(_.eq(this))

    private lazy val makerAndType: (Value, Value) = ClosureGraph.makerAndType(nodes, ims, vs => Construct(index, vs), rthis())
    lazy val maker: Value = makerAndType._1
    lazy val makerType: Value = makerAndType._2
  }


  case class Sum(
      level: Int,
      inductively: Option[Inductively],
      constructors: Seq[Constructor]) extends HeadCanonical {
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

  case class PatternLambda(id: Long, domain: Value, typ: Closure, cases: Seq[Case]) extends HeadCanonical

  case class PatternStuck(lambda: PatternLambda, stuck: StuckPos) extends Stuck

  case class Let(items: Seq[Value], body: Value) extends Syntaxial


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
      case g: Generic =>
        g.typ
      case Restricted(a, fs) =>
        fs.foldLeft(infer(a)) { (t, r) => t.restrict(r) }
      case Universe(level) => Universe.suc(level)
      case Up(a, b) => infer(a).up(b)
      case Function(domain, _, codomain) =>
        (infer(domain), infer(codomain(Generic(vgen(), domain)))) match {
          case (Universe(l1), Universe(l2)) => Universe(l1 max l2)
          case _ => logicError()
        }
      case r: Record =>
        Universe(r.level)
      case s: Sum =>
        Universe(s.level)
      case PathType(typ, _, _) =>
        infer(typ.apply(Dimension.Generic(vdgen())))
      case App(l1, a1) =>
        infer(l1).whnf match {
          case Function(_, _, c) =>
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

  object OpenMetaHeaded {

    def unapply(value: Value): Option[Meta] = {
      value match {
        case o: Meta => Some(o)
        case App(lambda, _) => unapply(lambda)
        case Projection(make, _) => unapply(make)
        case PatternStuck(_, stuck) => unapply(stuck)
        case PathApp(left, _) => unapply(left)
        case Coe(_, typ, _) =>
          // this rule is really wired...
          unapply(typ(Dimension.Generic(vdgen())).whnf)
        case Hcom(_, tp, _, _) => unapply(tp)
        case Restricted(a, _) => unapply(a)
        case _ => None
      }
    }
  }
}

