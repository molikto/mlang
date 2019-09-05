package mlang.compiler

import mlang.compiler.LongGen.Negative.{dgen, gen}
import mlang.compiler.Value.Formula.{Assignments, NormalForm}
import mlang.compiler.Value._
import mlang.utils.{Name, debug}

import scala.annotation.Annotation
import scala.collection.mutable

private[compiler] class stuck_pos extends Annotation

object Value {
  sealed trait Formula extends {
    import Formula.{And, Assignments, False, Neg, NormalForm, Or, True}
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
            case g: Formula.Generic => Neg(g)
            case And(left, right) => Or(negate(left), negate(right))
            case Or(left, right) => And(negate(left), negate(right))
            case Neg(u2) => u2
            case True => False
            case False => True
            case _: Formula.Internal => logicError()
          }
          unit match {
            case Formula.Generic(id) => Set(Set((id, false)))
            case r => negate(r).normalForm
          }
        case _: Formula.Internal => logicError()
      }
    }

    def restrict(lv: Value.Formula.Assignments): Formula = if (lv.isEmpty) this else {
      this match {
        case g:Formula.Generic => g.simplify(lv)
        case Formula.True => Formula.True
        case Formula.False => Formula.False
        case And(left, right) => And(left.restrict(lv), right.restrict(lv))
        case Or(left, right) => Or(left.restrict(lv), right.restrict(lv))
        case Formula.Derestricted(r, g) =>
          if (g.subsetOf(lv)) {
            r.restrict(lv -- g)
          } else {
            logicError()
          }
        case Neg(unit) => Neg(unit.restrict(lv))
      }
    }
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
    case class Derestricted(a: Formula, b: Formula.Assignments) extends Internal
  }

  implicit class MultiClosure(private val func: Seq[Value] => Value) extends AnyVal {
    def eq(b: MultiClosure): Boolean = func.eq(b.func)
    def apply() = func(Seq.empty)
    def apply(seq: Seq[Value]): Value = func(seq)
    def restrict(dav: Formula.Assignments): MultiClosure = MultiClosure(v => this(v.map(a => Derestricted(a, dav))).restrict(dav))
  }

  implicit class Closure(private val func: Value => Value) extends AnyVal {
    def eq(b: Closure): Boolean = func.eq(b.func)
    def apply(seq: Value): Value = func(seq)
    def restrict(dav: Formula.Assignments): Closure = Closure(d => func(Derestricted(d, dav)).restrict(dav))
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
    def restrict(dav: Formula.Assignments): AbsClosure = AbsClosure(d => func(Formula.Derestricted(d, dav)).restrict(dav))
  }

  type ClosureGraph = Seq[ClosureGraph.Node]
  object ClosureGraph {
    def restrict(graph: ClosureGraph, lv: Formula.Assignments): ClosureGraph =  {
      graph.map {
        case DependentWithMeta(ds, mc, c) =>
        DependentWithMeta(ds, mc, (a, b) => { val t = c(a, b.map(k => Derestricted(k, lv))); (t._1, t._2.restrict(lv)) })
        case IndependentWithMeta(ds, ms, typ) =>
          IndependentWithMeta(ds, ms, typ.restrict(lv))
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
  sealed trait Internal extends Value
  sealed trait Whnf extends Value
  sealed trait HeadCanonical extends Whnf
  sealed trait Redux extends Whnf {
    def reduce(): Option[Value]

    def reduceThenWhnfOrSelf() = reduce() match {
      case Some(r) => r.whnf
      case _ => this
    }
  }
  sealed trait CubicalUnstable extends Whnf // this value can reduce more, but only when restricted

  case class Derestricted(a: Value, asgn: Formula.Assignments) extends Internal

  sealed trait Referential extends Value {
    _from = this
    type Self <: Referential
    def getRestricted(asgs: Formula.Assignments): Self
    def lookupChildren(v: Referential): Option[Formula.Assignments]
  }

  sealed trait Reference extends Referential {
    override def toString: String = "Reference"
    var value: Value
  }


  sealed trait LocalReferential extends Referential {
    type Self <: LocalReferential
    private var state: mutable.Map[Formula.Assignments, LocalReferential] = null
    private var self: Formula.Assignments = null
    protected def clearSavedAfterValueChange() = {
      if (self != null && self.nonEmpty) logicError() // you don't want to do this
      state = null
    }

    protected def createNewEmpty(): Self

    protected def restrictAndInitContent(s: Self, assignments: Assignments): Unit
    def getRestricted(assigments: Formula.Assignments): Self = {
      if (state == null) {
        state = mutable.Map()
        self = Set.empty
      }
      val (mp, asg) = (state, self ++ assigments)
      mp.get(asg) match {
        case Some(r) => r.asInstanceOf[Self]
        case None =>
          val n = createNewEmpty()
          n.state = mp
          n.self = asg
          mp.put(asg, n)
          restrictAndInitContent(n, asg)
          n
      }
    }

    def lookupChildren(v: Referential): Option[Formula.Assignments] = {
      if (this.eq(v)) {
        Some(Set.empty)
      } else {
        assert(self == null || self.isEmpty)
        if (state != null) state.find(_._2.eq(v)).map(_._1)
        else None
      }
    }
  }

  sealed trait MetaState
  object MetaState {
    case class Closed(v: Value) extends MetaState
    case class Open(id: Long, typ: Value) extends MetaState
  }
  case class Meta(@polarized_mutation private var _state: MetaState) extends LocalReferential {
    def solved: Value = state.asInstanceOf[MetaState.Closed].v
    def isSolved: Boolean = state.isInstanceOf[MetaState.Closed]
    def state_=(a: MetaState) = {
      clearSavedAfterValueChange()
      _state = a
    }
    def state = _state

    override type Self = Meta
    override protected def createNewEmpty(): Meta = Meta(null)
    override protected def restrictAndInitContent(s: Meta, assignments: Assignments): Unit = state match {
      case MetaState.Closed(v) => s._state = MetaState.Closed(v.restrict(assignments))
      case MetaState.Open(id, typ) => s._state = MetaState.Open(id, typ.restrict(assignments))
    }
  }


  case class GlobalReference(@lateinit var value: Value) extends Reference {
    override type Self = GlobalReference
    override def getRestricted(asgs: Assignments): GlobalReference = this
    def lookupChildren(v: Referential): Option[Formula.Assignments] = if (this.eq(v)) Some(Set.empty) else None
  }

  case class LocalReference(@lateinit private var _value: Value) extends LocalReferential with Reference {

    override def value_=(a: Value) = {
      clearSavedAfterValueChange()
      _value = a
    }
    override def value = _value

    override type Self = LocalReference
    override protected def createNewEmpty(): LocalReference = LocalReference(null)
    override protected def restrictAndInitContent(s: LocalReference, assignments: Assignments) =
      s._value = value.restrict(assignments)
  }

  case class Generic(id: Long, @lateinit private var _typ: Value) extends LocalReferential {

    def typ_=(a: Value) = {
      clearSavedAfterValueChange()
      _typ = a
    }
    def typ = _typ

    override type Self = Generic
    override protected def createNewEmpty(): Generic = Generic(id, null)
    override protected def restrictAndInitContent(s: Generic, assignments: Assignments) =
      s._typ = typ.restrict(assignments)
  }

  object WhnfOpenMetaHeaded {

    def unapply(value: Value): Option[Meta] = {
      value match {
        case _: HeadCanonical => None
        case _: CubicalUnstable => None
        case _: Generic => None
        case o: Meta => Some(o)
        case App(lambda, _) => unapply(lambda)
        case Projection(make, _) => unapply(make)
        case PatternRedux(_, stuck) => unapply(stuck)
        case PathApp(left, _) => unapply(left)
        case VProj(_, m, _) => unapply(m)
        case Transp(_, typ, _) =>
          // FIXME this rule is really wired...
          unapply(typ(Formula.Generic(dgen())).whnf)
        case Hcom(tp, _, _) => unapply(tp)
        case _: Com => logicError()
        case _: Reference => logicError()
        case _: Maker => logicError()
        case _: Internal => logicError()
      }
    }
  }

  object ReferenceTail {
    def rec(a: Value, ref: Option[Reference]): Option[(Value, Option[Reference])] = a match {
      case Meta(MetaState.Closed(v)) => rec(v, ref)
      case r: Reference => rec(r.value, Some(r))
      case els => Some((els, ref))
    }
    def unapply(a: Value): Option[(Value, Option[Reference])] = rec(a, None)
  }

  object GenericOrOpenMeta {
    def unapply(a: Value): Option[LocalReferential] = a match {
      case g: Generic => Some(g)
      case m@Meta(_: MetaState.Open) => Some(m)
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
  case class App(@stuck_pos lambda: Value, argument: Value) extends Redux {
    def reduce(): Option[Value] = {
      // FIXME cubicaltt will also work if lambda is a trans lambda or a comp lambda
      lambda match {
        case Lambda(closure) =>
          Some(closure(argument))
        case p : PatternLambda =>
          Some(PatternRedux(p, argument))
        case _ =>
          None
      }
    }
  }
  def Apps(maker: Value, values: Seq[Value]) : Value = values.foldLeft(maker) { (m: Value, v: Value) => Value.App(m, v) }
  case class Lambda(closure: Closure) extends HeadCanonical
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
  // FIXME seems we must have domain here? --- or when we don't have lambda head?
  case class PatternLambda(id: Long, domain: Value, typ: Closure, cases: Seq[Case]) extends HeadCanonical
  case class PatternRedux(lambda: PatternLambda, @stuck_pos stuck: Value) extends Redux {
    // FIXME cubical tt will also work if argument is a hcomp
    def reduce(): Option[Value] = {
      // using first match is even ok for overlapping ones
      var res: Value = null
      var cs = lambda.cases
      while (cs.nonEmpty && res == null) {
        res = cs.head.tryApp(stuck).orNull
        cs = cs.tail
      }
      Option(res)
    }
  }


  case class Inductively(id: Long, level: Int) {
    def restrict(lv: Formula.Assignments): Inductively = this
  }

  case class Record(
      inductively: Option[Inductively],
      names: Seq[Name],
      ims: Seq[Boolean],
      nodes: ClosureGraph) extends HeadCanonical {
    assert(names.size == nodes.size)

    private def rthis(): Value = LocalReference(this)

    private lazy val makerAndType: (Value, Value) = ClosureGraph.makerAndType(nodes, ims, vs => Make(vs), rthis())
    lazy val maker: Value = makerAndType._1
    lazy val makerType: Value = makerAndType._2

    def projectedType(values: Value, name: Int): Value = {
      ClosureGraph.get(nodes, name, i => Projection(values, i))
    }
  }
  case class Make(values: Seq[Value]) extends HeadCanonical
  // FIXME do away with this
  case class Maker(value: Value, field: Int) extends Value
  case class Projection(@stuck_pos make: Value, field: Int) extends Redux {
    def reduce(): Option[Value] = {
      make match {
        case Make(vs) => Some(vs(field))
        case _ => None
      }
    }
  }

  case class Construct(name: Int, vs: Seq[Value]) extends HeadCanonical
  case class Constructor(name: Name, ims: Seq[Boolean], nodes: ClosureGraph) {
    private[Value] var _sum: Sum = _
    private def rthis(): Value = LocalReference(_sum)

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
  case class PathApp(@stuck_pos left: Value, @stuck_pos dimension: Formula) extends Redux {
    def reduce(): Option[Value] = left match {
      case PathLambda(c) =>
        Some(c(dimension))
      case a =>
        // I think both yacctt use open variables with types, and an `inferType` thing
        def constantCase(isOne: Boolean) = {
          a.infer.whnf match {
            case PathType(_, left, right) =>
              Some(if (isOne) right else left)
            case _ => logicError()
          }
        }
        dimension.normalForm match {
          case NormalForm.True =>
            constantCase(true)
          case NormalForm.False =>
            constantCase(false)
          case _ =>
            None
        }
    }
  }

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
  case class Transp(direction: Formula, @stuck_pos tp: AbsClosure.StuckPos, base: Value) extends Redux {
    override def reduce(): Option[Value] = {
      if (direction.normalForm == Formula.NormalForm.True) {
        Some(base)
      } else {
        // IMPL
        ???
      }
    }
  }
  case class Com(@stuck_pos tp: AbsClosure.StuckPos, base: Value, faces: Seq[Face]) extends Redux {
    override def reduce(): Option[Value] = {
      // IMPL
      ???
    }
  }

  case class Hcom(@stuck_pos tp: Value, base: Value, faces: Seq[Face]) extends Redux {
    override def reduce(): Option[Value] = {
      faces.find(_.restriction.normalForm == NormalForm.True) match {
        case Some(t) => Some(t.body(Formula.True))
        case None =>
          // IMPL
          None
      }
    }
  }

  case class VType(x: Value.Formula, a: Value, b: Value, e: Value) extends CubicalUnstable
  case class VMake(x: Value.Formula, m: Value, n: Value) extends CubicalUnstable
  case class VProj(x: Value.Formula, @stuck_pos m: Value, f: Value) extends Redux {
    override def reduce(): Option[Value] = ???
  }
}


sealed trait Value {
  final override def equals(obj: Any): Boolean = throw new IllegalArgumentException("Values don't have equal. Either call eq or do conversion checking")

  @cached_mutation private[Value] var _from: Value = _
  @cached_mutation private[Value] var _whnf: Value = _

  def from: Value = if (_from == null) this else _from

  // it is ensured that if the value is not reducable, it will return the same reference
  def whnf: Value = {
    def eqFaces(f1: Seq[Face], f2: Seq[Face]): Boolean = f1.eq(f2) || (f1.size == f2.size && f1.zip(f2).forall(p => {
      p._1.restriction == p._2.restriction && p._1.body.eq(p._2.body)
    }))
    if (_whnf == null) {
      val current = this
      var changed = true
      while (changed) {

      }
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
        case app@App(lambda, argument) =>
          // FIXME don't do this equals stuff!!!
          def app2(lambda: Value, argument: Value): Value = {
            lambda match {
              case Lambda(closure) =>
                closure(argument).whnf
              case p : PatternLambda =>
                PatternRedux(p, argument.whnf).reduceThenWhnfOrSelf()
              case _ =>
                App(lambda, argument)
            }
          }
          app2(lambda.whnf, argument) match {
            case App(l2, a2) if lambda.eq(l2) && a2.eq(argument) => this
            case a => a
          }
        case pat@PatternRedux(lambda, stuck) =>
          PatternRedux(lambda, stuck.whnf).reduceThenWhnfOrSelf() match {
            case PatternRedux(l2, s2) if lambda.eq(l2) && stuck.eq(s2) => this
            case a => a
          }
        case pro@Projection(make, field) =>
          Projection(make.whnf, field).reduceThenWhnfOrSelf() match {
            case Projection(m2, f2) if make.eq(m2) && field == f2 => this
            case a => a
          }
        case PathApp(left, dimension) =>
          // we MUST perform this, because this doesn't care
          PathApp(left.whnf, dimension).reduceThenWhnfOrSelf() match {
            case PathApp(l2, s2) if left.eq(l2) && dimension == s2 => this
            case a => a.whnf
          }
        case transp@Transp(direction, tp, base) =>
          // kan ops case analysis on tp, so they perform their own whnf
          transp.reduceThenWhnfOrSelf() match {
            case Transp(d2, t2, b2) if d2 == direction && t2.eq(tp) && base.eq(b2) => this
            case a => a
          }
        case com@Com(tp, base, faces) =>
          com.reduceThenWhnfOrSelf() match {
            case Com(t2, b2, f2) if tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
            case a => a
          }
        case hcom@Hcom(tp, base, faces) =>
          hcom.reduceThenWhnfOrSelf() match {
            case Hcom(t2, b2, f2) if tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
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
        case _: Internal =>
          logicError()
      }
      // because some values is shared, it means the solved ones is not created for this whnf, we don't say this
      // is from us
      if (!candidate.eq(candidate._from)) { // FIXME these are already defined ones
        if (!candidate.eq(this)) {
          candidate._from = this
        }
      }

      candidate match {
        case Value.WhnfOpenMetaHeaded(_) =>
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
    case Hcom(tp, base, faces) =>
      Hcom(tp.restrict(lv), base.restrict(lv), Face.restrict(faces, lv))
    case Com(tp, base, faces) =>
      Com(tp.restrict(lv), base.restrict(lv), Face.restrict(faces, lv))
    case Maker(value, field) =>
      Maker(value.restrict(lv), field)
    case Projection(make, field) =>
      Projection(make.restrict(lv), field)
    case PatternRedux(lambda, stuck) =>
      PatternRedux(lambda.restrict(lv).asInstanceOf[PatternLambda], stuck.restrict(lv))
    case PathApp(left, stuck) =>
      PathApp(left.restrict(lv), stuck.restrict(lv))
    case VType(x, a, p, e) =>
      VType(x.restrict(lv), a.restrict(lv), p.restrict(lv), e.restrict(lv))
    case VMake(x, m, n) =>
      VMake(x.restrict(lv), m.restrict(lv), n.restrict(lv))
    case VProj(x, m, f) =>
      VProj(x.restrict(lv), m.restrict(lv), f.restrict(lv))
    case Derestricted(v, lv0) =>
      if (lv0.subsetOf(lv)) {
        v.restrict(lv -- lv0)
      } else {
        logicError()
      }
    case g: Referential =>
      g.getRestricted(lv)
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
        // l1 cannot be a actual lambda, the real blocker of whnf is only open reference/meta
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
      case PatternRedux(l1, s1) =>
        l1.typ(s1)
      case PathApp(l1, d1) =>
        l1.infer.whnf match {
          case PathType(typ, _, _) => typ(d1)
          case _ => logicError()
        }
      case h: Hcom => h.tp
      case t: Transp => t.tp(Formula.True)
      case h: Com => h.tp(Formula.True)
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

object BuildIn {
  var equiv: Value = null
  var fiber_at: Value = null
  var fiber_at_ty: Value = null
}
