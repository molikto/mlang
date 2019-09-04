package mlang.compiler

import mlang.utils.{DisjointSet, Name, debug, warn}

import scala.collection.mutable
import LongGen.Negative.{dgen, gen}
import Value._
import mlang.compiler.Value.Formula.NormalForm

import scala.annotation.Annotation

private[compiler] class stuck_pos extends Annotation

object Value {
  sealed trait Formula extends {
    import Formula.{NormalForm, And, Or, Neg, True, False, Assignments, Assignment}
    def normalForm: NormalForm  = {
      def merge(a: NormalForm, b: NormalForm): NormalForm = {
        def properSupersetOfAny(c: Assignments, g: NormalForm) = b.exists(g => g.subsetOf(c) && g != c)
        a.filter(c => !properSupersetOfAny(c, b)) ++ b.filter(c => !properSupersetOfAny(c, a))
      }
      this match {
        case True => NormalForm.True
        case False => NormalForm.False
        case Formula.Generic(id) => Set(Set((id, true)))
        case And(left, right) =>
          val ln = left.normalForm.toSeq
          val rn = right.normalForm.toSeq
          ln.flatMap(i => rn.map(r => Set(i ++ r) : NormalForm)).foldLeft(NormalForm.False) { (a, b) => merge(a, b)}
        case Or(left, right) => merge(left.normalForm, right.normalForm)
        case Neg(unit) =>
          def negate(f: Formula): Formula = f match {
            case g: Generic => Neg(g)
            case And(left, right) => Or(negate(left), negate(right))
            case Or(left, right) => And(negate(left), negate(right))
            case Neg(u2) => u2
            case True => False
            case False => True
            case _ => logicError()
          }
          unit match {
            case Formula.Generic(id) => Set(Set((id, false)))
            case r => negate(r).normalForm
          }
        case _ => logicError()
      }
    }
    def restrict(lv: Value.Formula.Assignments): Formula = ???
  }

  object Formula {
    def satisfiable(rs: Assignments): Boolean = rs.map(_._1).size == rs.size

    type Assignment = (Long, Boolean)
    type Assignments = Set[Assignment]
    type NormalForm = Set[Assignments]
    object NormalForm {
      val True: NormalForm = Set(Set.empty)
      val False: NormalForm = Set.empty
    }
    case class Generic(id: Long) extends Formula {
      def simplify(asgs: Assignments): Formula = asgs.find(_._1 == id) match {
        case Some(a) => if (a._2) True else False
        case None => this
      }
    }
    object True extends Formula
    object False extends Formula
    case class And(left: Formula, right: Formula) extends Formula
    case class Or(left: Formula, right: Formula) extends Formula
    case class Neg(unit: Formula) extends Formula
    sealed trait Internal extends Formula
  }

  implicit class MultiClosure(private val func: Seq[Value] => Value) extends AnyVal {
    def eq(b: MultiClosure): Boolean = func.eq(b.func)
    def apply() = func(Seq.empty)
    def apply(seq: Seq[Value]): Value = func(seq)
    def restrict(dav: Formula.Assignments): MultiClosure = ???
  }

  implicit class Closure(private val func: Value => Value) extends AnyVal {
    def eq(b: Closure): Boolean = func.eq(b.func)
    def apply(seq: Value): Value = func(seq)
    def restrict(dav: Formula.Assignments): Closure = ???
  }

  object Closure {
    def apply(a: Value): Closure = Closure(_ => a)
  }

  object AbsClosure {
    def apply(a: Value): AbsClosure = AbsClosure(_ => a)
    type StuckPos = AbsClosure
  }

  implicit class AbsClosure(private val func: Formula => Value) extends AnyVal {
    def eq(b: AbsClosure): Boolean = func.eq(b.func)
    def apply(seq: Formula): Value = func(seq)
    def mapd(a: (Value, Formula) => Value): AbsClosure = AbsClosure(d => a(this(d), d))
    def map(a: Value => Value): AbsClosure = AbsClosure(d => a(this(d)))
    def restrict(dav: Formula.Assignments): AbsClosure = ???
  }

  type ClosureGraph = Seq[ClosureGraph.Node]
  object ClosureGraph {
    def restrict(graph: ClosureGraph, lv: Formula.Assignments): ClosureGraph = ??? /* {
      graph.map {
        case DependentWithMeta(ds, mc, c) =>
        DependentWithMeta(ds, mc, (a, b) => { val t = c(a, b.map(k => Derestricted(k, lv))); (t._1, t._2.restrict(lv)) })
        case IndependentWithMeta(ds, ms, typ) =>
          IndependentWithMeta(ds, ms, typ.restrict(lv))
        case _ => logicError()
      }
    }
    */

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

    private case class DependentWithMeta(dependencies: Seq[Int], metaCount: Int, closure: (Seq[Value.Meta], Seq[Value]) => (Seq[Value.Meta], Value)) extends Dependent

    private case class IndependentWithMeta(dependencies: Seq[Int], metas: Seq[Value.Meta], typ: Value) extends Independent {
    }

    private case class ValuedWithMeta(dependencies: Seq[Int], metas: Seq[Value.Meta], typ: Value, value: Value) extends Valued {
    }

    def createMetaAnnotated(nodes: Seq[(Seq[Int], Int, (Seq[Value.Meta], Seq[Value]) => (Seq[Value.Meta], Value))]): ClosureGraph = {
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


    def inferLevel(nodes: ClosureGraph): Int = {
      var level = 0
      var i = 0
      var g = nodes
      while (i < g.size) {
        val t = g(i).independent.typ
        level = t.inferLevel max level
        val ge = Generic(gen(), t)
        g = ClosureGraph.reduce(g, i, ge)
        i += 1
      }
      level
    }

    def reduce(from: ClosureGraph, i: Int, a: Value): ClosureGraph = {
      from(i) match {
        case IndependentWithMeta(ds, mss, typ) =>
          val ns = ValuedWithMeta(ds, mss, typ, a)
          val mms: Seq[Value.Meta] = from.flatMap {
            case DependentWithMeta(_, ms, _) => (0 until ms).map(_ => null)
            case IndependentWithMeta(_, ms, _) => ms
            case ValuedWithMeta(_, ms, _, _) => ms
          }
          val vs = from.indices.map(j => if (j == i) a else from(j) match {
            case ValuedWithMeta(_, _, _, v) => v
            case _ => null
          })
          from.map {
            case DependentWithMeta(dss, _, c) if dss.forall(j => vs(j) != null) =>
              val t = c(mms, vs)
              IndependentWithMeta(dss, t._1, t._2)
            case i =>
              i
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



  // these serve the purpose of recovering syntax
  sealed trait Syntaxial extends Value
  sealed trait Internal extends Value
  sealed trait Whnf extends Value
  sealed trait HeadCanonical extends Whnf
  sealed trait Stuck extends Whnf
  sealed trait CubicalUnstable extends Whnf // this value can reduce more, but only when restricted


  sealed trait MetaState
  object MetaState {
    case class Closed(v: Value) extends MetaState
    case class Open(id: Long, typ: Value) extends MetaState
  }
  case class Meta(@polarized_mutation var state: MetaState) extends Syntaxial {
    def solved: Value = state.asInstanceOf[MetaState.Closed].v
    def isSolved: Boolean = state.isInstanceOf[MetaState.Closed]

    _from = this
  }

  case class Restricted(a: Value, asgn: Formula.Assignments) extends Syntaxial
  case class Derestricted(a: Value, asgn: Formula.Assignments) extends Internal

  case class Reference(@lateinit var value: Value) extends Syntaxial {
    _from = this
    override def toString: String = "Reference"
  }

  case class Let(items: Seq[Reference], body: Value) extends Syntaxial

  case class Generic(id: Long, @lateinit var typ: Value) extends Stuck {
    _from = this
  }

  object OpenMetaHeadedWhnf {

    def unapply(value: Value): Option[Meta] = {
      value match {
        case _: HeadCanonical => None
        case _: CubicalUnstable => None
        case _: Generic => None
        case o: Meta => Some(o)
        case App(lambda, _) => unapply(lambda)
        case Projection(make, _) => unapply(make)
        case PatternStuck(_, stuck) => unapply(stuck)
        case PathApp(left, _) => unapply(left)
        case VProj(_, m, _) => unapply(m)
        case Transp(_, typ, _) =>
          // FIXME this rule is really wired...
          unapply(typ(Formula.Generic(dgen())).whnf)
        case Hcom(_, tp, _, _) => unapply(tp)
        //case Restricted(a, _) => unapply(a)
        case _: Com => logicError()
        case _: Syntaxial => logicError()
        case _: Internal => logicError()
      }
    }
  }

  object ReferenceTail {
    def rec(a: Value, ref: Option[Reference]): Option[(Value, Option[Reference])] = a match {
      case Meta(MetaState.Closed(v)) => rec(v, ref)
      case r@Reference(t) => rec(t, Some(r))
      case els => Some((els, ref))
    }
    def unapply(a: Value): Option[(Value, Option[Reference])] = rec(a, None)
  }

  object GenericOrOpenMeta {
    def unapply(a: Value): Option[Value] = a match {
      case g: Generic => Some(g)
      case Meta(_: MetaState.Open) => Some(a)
      case _ => None
    }
  }


  case class Universe(level: Int) extends HeadCanonical

  object Universe {
    val TypeInType = true
    def suc(i: Int) = Universe(if (TypeInType) 0 else i)
    def level0 = Universe(0)
    def level1 = Universe(if (TypeInType) 0 else 1)
  }

  case class Function(domain: Value, impict: Boolean, codomain: Closure) extends HeadCanonical
  case class App(@stuck_pos lambda: Value, argument: Value) extends Stuck
  def Apps(maker: Value, values: Seq[Value]) : Value = values.foldLeft(maker) { (m: Value, v: Value) => Value.App(m, v) }
  case class Lambda(closure: Closure) extends HeadCanonical
  // FIXME seems we must have domain here?
  case class Case(pattern: Pattern, closure: MultiClosure) {
    private def extract(pattern: Pattern, v: Value): Option[Seq[Value]] = {
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
        Some(vs.toSeq)
      } else {
        None
      }
    }
    def tryApp(v: Value): Option[Value] = extract(pattern, v).map(a => closure(a))
  }
  case class PatternLambda(id: Long, domain: Value, typ: Closure, cases: Seq[Case]) extends HeadCanonical
  case class PatternStuck(lambda: PatternLambda, @stuck_pos stuck: Value) extends Stuck


  case class Inductively(id: Long, level: Int) {
    def restrict(lv: Formula.Assignments): Inductively = this
  }

  case class Record(
      inductively: Option[Inductively],
      names: Seq[Name],
      ims: Seq[Boolean],
      nodes: ClosureGraph) extends HeadCanonical {
    assert(names.size == nodes.size)

    private def rthis(): Value = Reference(this)

    private lazy val makerAndType: (Value, Value) = ClosureGraph.makerAndType(nodes, ims, vs => Make(vs), rthis())
    lazy val maker: Value = makerAndType._1
    lazy val makerType: Value = makerAndType._2

    def projectedType(values: Value, name: Int): Value = {
      ClosureGraph.get(nodes, name, i => Projection(values, i))
    }
  }
  case class Make(values: Seq[Value]) extends HeadCanonical
  case class Maker(value: Value, field: Int) extends Syntaxial
  case class Projection(@stuck_pos make: Value, field: Int) extends Stuck

  case class Construct(name: Int, vs: Seq[Value]) extends HeadCanonical
  case class Constructor(name: Name, ims: Seq[Boolean], nodes: ClosureGraph) {
    private[Value] var _sum: Sum = _
    private def rthis(): Value = Reference(_sum)

    private def index = _sum.constructors.indexWhere(_.eq(this))

    private lazy val makerAndType: (Value, Value) = ClosureGraph.makerAndType(nodes, ims, vs => Construct(index, vs), rthis())
    lazy val maker: Value = makerAndType._1
    lazy val makerType: Value = makerAndType._2
  }
  case class Sum(
      inductively: Option[Inductively],
      constructors: Seq[Constructor]) extends HeadCanonical {
    for (c <- constructors) {
      c._sum = this
    }
  }

  case class PathType(typ: AbsClosure, left: Value, right: Value) extends HeadCanonical
  case class PathLambda(body: AbsClosure) extends HeadCanonical
  case class PathApp(@stuck_pos left: Value, @stuck_pos dimension: Formula) extends Stuck

  object Face {
    def restrict(faces: Seq[Face], lv: Formula.Assignments) = {
      faces.flatMap(n => {
        val r = n.restriction.restrict(lv)
        val nf = r.normalForm
        if (nf == Formula.NormalForm.False) {
          None
        } else {
          Some(Face(r, n.body.restrict(lv)))
        }
      })
    }
  }
  case class Face(restriction: Formula, body: AbsClosure)
  case class Transp(direction: Formula, @stuck_pos tp: AbsClosure.StuckPos, base: Value) extends Stuck
  case class Com(direction: Formula, @stuck_pos tp: AbsClosure.StuckPos, base: Value, faces: Seq[Face]) extends Stuck
  case class Hcom(direction: Formula, @stuck_pos tp: Value, base: Value, faces: Seq[Face]) extends Stuck

  case class VType(x: Value.Formula, a: Value, b: Value, e: Value) extends CubicalUnstable
  case class VMake(x: Value.Formula, m: Value, n: Value) extends CubicalUnstable
  case class VProj(x: Value.Formula, @stuck_pos m: Value, f: Value) extends Stuck
}


sealed trait Value {
  final override def equals(obj: Any): Boolean = throw new IllegalArgumentException("Values don't have equal. Either call eq or do conversion checking")

  @cached_mutation private[Value] var _from: Value = _
  @cached_mutation private[Value] var _whnf: Value = _

  def from: Value = if (_from == null) this else _from

  def whnf: Value = {
    import ValueOps._
    if (_whnf == null) {
      // TODO can we sort by restriction first?
      def eqFaces(f1: Seq[Face], f2: Seq[Face]): Boolean = ???
      /*
        f1.eq(f2) || (f1.size == f2.size && f1.zip(f2).forall(p => {
        p._1.restriction.sameRestrict(p._2.restriction) && p._1.body.eq(p._2.body)
      }))
       */
      val candidate = this match {
        case a: HeadCanonical =>
          a
        case r: Reference =>
          r.value.whnf
        case o: Generic =>
          o
        case m: Meta =>
          m.state match {
            case MetaState.Closed(v) => v.whnf
            case _: MetaState.Open => m
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
          // FIXME we really needs to cleanup these stuff
          def app2(lambda: Value, argument: Value, returns: Value => Value = id): Value = {
            lambda match {
              case Lambda(closure) =>
                returns(closure(argument))
              case p : PatternLambda =>
                split(p, argument.whnf, returns)
              case _ =>
                App(lambda, argument)
            }
          }
          app2(lambda.whnf, argument.whnf, _.whnf) match {
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
        case Transp(direction, tp, base) =>
          // kan ops case analysis on tp, so they perform their own whnf
          transp(direction, tp, base, _.whnf) match {
            case Transp(d2, t2, b2) if d2 == direction && t2.eq(tp) && base.eq(b2) => this
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
        case VType(x, a, b, _) =>
//          x match {
//            case _: Formula.Generic => this
//            case Formula.False => a.whnf
//            case Formula.True => b.whnf
//            case _: Formula.Internal => logicError()
//          }
          ???
        case VMake(x, m, n) =>
//          x match {
//            case g: Formula.Generic => this
//            case Formula.False => m
//            case Formula.True => n
//            case _: Formula.Internal => logicError()
//          }
          ???
        case VProj(x, m, f) =>
//          x match {
//            case g: Formula.Generic =>
//              val mw = m.whnf
//              @inline def fallback() = if (mw.eq(m)) this else VProj(x, mw, f)
//              mw match {
//                case VMake(x2, _, n) =>
//                  assert(x == x2)
//                  n.whnf
//                case _ => fallback()
//              }
//            case Formula.False => app(f, m).whnf
//            case Formula.True => m.whnf
//            case _: Formula.Internal => logicError()
//          }
          ???
      case Restricted(a, restriction) =>
        if (debug.enabled) assert(Formula.satisfiable(restriction))
        if (restriction.isEmpty) {
          a.whnf
        } else {
          a match {
            case GenericOrOpenMeta(it) => Restricted(it, restriction) // stop case
            case _ => a.deref().restrict(restriction).whnf
          }
        }
        case _: Internal =>
          logicError()
      }
      // because some values is shared, it means the solved ones is not created for this whnf, we don't say this
      // is from us
      if (!candidate.eq(candidate._from)) { // FIXME these are already defined ones
        if (!candidate.eq(this)) {
          candidate._from = this
        } else {
          assert(candidate._from == null)
        }
      }
      candidate match {
        case Value.OpenMetaHeadedWhnf(_) =>
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

  // FIXME how does it interact with recursive references?
  def restrict(lv: Value.Formula.Assignments): Value = if (lv.isEmpty) this else this match {
    case u: Universe => u
    case Function(domain, im, codomain) =>
      Function(domain.restrict(lv), im, codomain.restrict(lv))
    case Record(inductively, ms, ns, nodes) =>
      Record(inductively.map(_.restrict(lv)), ms, ns, ClosureGraph.restrict(nodes, lv))
    case Make(values) =>
      Make(values.map(_.restrict(lv)))
    case Construct(name, vs) =>
      Construct(name, vs.map(_.restrict(lv)))
    case Sum(inductively, constructors) =>
      Sum(inductively.map(_.restrict(lv)), constructors.map(n => Constructor(n.name, n.ims, ClosureGraph.restrict(n.nodes, lv))))
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
    case Transp(direction, tp, base) =>
      Transp(direction.restrict(lv), tp.restrict(lv), base.restrict(lv))
    case Hcom(direction, tp, base, faces) =>
      Hcom(direction.restrict(lv), tp.restrict(lv), base.restrict(lv), Face.restrict(faces, lv))
    case Com(direction, tp, base, faces) =>
      Com(direction.restrict(lv), tp.restrict(lv), base.restrict(lv), Face.restrict(faces, lv))
    case Maker(value, field) =>
      Maker(value.restrict(lv), field)
    case Projection(make, field) =>
      Projection(make.restrict(lv), field)
    case PatternStuck(lambda, stuck) =>
      PatternStuck(lambda.restrict(lv).asInstanceOf[PatternLambda], stuck.restrict(lv))
    case PathApp(left, stuck) =>
      PathApp(left.restrict(lv), stuck.restrict(lv))
    case VType(x, a, p, e) =>
      VType(x.restrict(lv), a.restrict(lv), p.restrict(lv), e.restrict(lv))
    case VMake(x, m, n) =>
      VMake(x.restrict(lv), m.restrict(lv), n.restrict(lv))
    case VProj(x, m, f) =>
      VProj(x.restrict(lv), m.restrict(lv), f.restrict(lv))
    case Let(items, body) =>
      Let(items.map(_.restrict(lv).asInstanceOf[Reference]), body.restrict(lv))
    case Derestricted(v, lv0) =>
      assert(lv.eq(lv0))
      v
    case r: Restricted =>
      Restricted(r, lv)
    case g: Generic =>
      Restricted(g, lv)
    case o: Reference =>
      Restricted(o, lv)
    case o: Meta =>
      Restricted(o, lv)
  }


  def inferLevel: Int = infer match {
    case Universe(l) => l
    case _ => logicError()
  }

  // it is like in type directed conversion checking, this works because we always call infer on whnf, so neutural values
  // can infer it's type
  def infer: Value = {
    whnf match {
      case g: Generic =>
        g.typ
      //      case Restricted(a, fs) =>
      //        fs.foldLeft(infer(a)) { (t, r) => t.restrict(r) }
      case Universe(level) => Universe.suc(level)
      case Function(domain, _, codomain) =>
        (domain.infer, codomain(Generic(gen(), domain)).infer) match {
          case (Universe(l1), Universe(l2)) => Universe(l1 max l2)
          case _ => logicError()
        }
      case VType(_, a, b, _) =>
        (a.infer, b.infer) match {
          case (Universe(l1), Universe(l2)) => Universe(l1 max l2)
          case _ => logicError()
        }
      case r: Record =>
        r.inductively.map(a => Universe(a.level)).getOrElse(Universe(ClosureGraph.inferLevel(r.nodes)))
      case s: Sum =>
        s.inductively.map(a => Universe(a.level)).getOrElse(
          Universe(if (s.constructors.isEmpty) 0 else s.constructors.map(c => ClosureGraph.inferLevel(c.nodes)).max))
      case PathType(typ, _, _) =>
        typ.apply(Formula.Generic(dgen())).infer
      case App(l1, a1) =>
        l1.infer.whnf match {
          case Function(_, _, c) =>
            c(a1)
          case _ => logicError()
        }
      case Projection(m1, f1) =>
        m1.infer.whnf match {
          case rr: Record  => rr.projectedType(m1, f1)
          case _ => logicError()
        }
      case PatternStuck(l1, s1) =>
        l1.typ(s1)
      case PathApp(l1, d1) =>
        l1.infer.whnf match {
          case PathType(typ, _, _) => typ(d1)
          case _ => logicError()
        }
      case _ => logicError()
    }
  }


  def deref(): Value = this match {
    case r: Reference => r.value.deref()
    case Meta(c: MetaState.Closed) => c.v.deref()
    case _: Internal => logicError()
    case _ => this
  }

  def makerType(i: Int): Value = this.whnf match {
    case s: Sum => s.constructors(i).makerType
    case v: Record => v.makerType
    case _ => logicError()
  }
}


object ValueOps {

  def app(lambda: Value, argument: Value, returns: Value => Value = id): Value = {
    // FIXME cubicaltt will also work if lambda is a trans lambda or a comp lambda
    lambda match {
      case Lambda(closure) =>
        returns(closure(argument))
      case p : PatternLambda =>
        split(p, argument, returns)
      case _ =>
        App(lambda, argument)
    }
  }


  // FIXME cubical tt will also work if argument is a hcomp
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

  def papp(l: Value, d: Formula, returns: Value => Value = id): Value = l match {
    case PathLambda(c) =>
      returns(c(d))
    case a =>
      // I think both yacctt use open variables with types, and an `inferType` thing
      def constantCase(isOne: Boolean) = {
        a.infer.whnf match {
          case PathType(_, left, right) =>
            returns(if (isOne) right else left)
          case _ => logicError()
        }
      }
      d.normalForm match {
        case NormalForm.True =>
          constantCase(true)
        case NormalForm.False =>
          constantCase(false)
        case _ =>
          PathApp(l, d)
      }
  }

  def id(v: Value) = v

  def transp(pair: Formula, typ: AbsClosure, base: Value, returns: Value => Value = id): Value = ???


  def com(pair: Formula, typ: AbsClosure, base: Value, restriction0: Seq[Face], returns: Value => Value = id): Value = ???

  def hcom(pair: Formula, typ: Value, base: Value, restriction0: Seq[Face], returns: Value => Value = id): Value = ???
}

object BuildIn {
  var equiv: Value = null
  var fiber_at: Value = null
  var fiber_at_ty: Value = null
}
