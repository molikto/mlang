package mlang.compiler

import mlang.compiler.LongGen.Negative.{dgen, gen}
import mlang.compiler.Value.Formula.{Assignments, NormalForm}
import mlang.compiler.Value.{AbsClosure, _}
import mlang.utils.{Name, debug}

import scala.annotation.Annotation
import scala.collection.mutable

private[compiler] class stuck_pos extends Annotation

case class ImplementationLimitationCannotRestrictOpenMeta() extends Exception

object Value {
  sealed trait Formula extends {
    import Formula.{And, Assignments, False, Neg, NormalForm, Or, True}
    def names: Set[Long] = {
      this match {
        case Formula.Generic(id) => Set(id)
        case Formula.True => Set.empty
        case Formula.False => Set.empty
        case And(left, right) => left.names ++ right.names
        case Or(left, right) => left.names ++ right.names
        case Neg(unit) => unit.names
        case _: Formula.Internal => logicError()
      }
    }

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
        case Formula.Derestricted(r, g) => if (g.subsetOf(lv)) r.restrict(lv -- g) else logicError()
        case Neg(unit) => Neg(unit.restrict(lv))
      }
    }
  }

  object Formula {

    type Assignment = (Long, Boolean)
    type Assignments = Set[Assignment]
    object Assignments {
      def satisfiable(rs: Assignments): Boolean = rs.map(_._1).size == rs.size
    }
    type NormalForm = Set[Assignments]
    object NormalForm {
      def satisfiable(_2: NormalForm): Boolean = _2.exists(Assignments.satisfiable)

      val True: NormalForm = Set(Set.empty)
      val False: NormalForm = Set.empty
    }
    object Generic {
      val HACK = Generic(0)
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
    private[Value] def supportShallow(): SupportShallow = func(Generic.HACKS).supportShallow()
    def eq(b: MultiClosure): Boolean = func.eq(b.func)
    def apply() = func(Seq.empty)
    def apply(seq: Seq[Value]): Value = func(seq)
    def restrict(dav: Formula.Assignments): MultiClosure = MultiClosure(v => this(v.map(a => Derestricted(a, dav))).restrict(dav))
  }

  implicit class Closure(private val func: Value => Value) extends AnyVal {
    private[Value] def supportShallow(): SupportShallow = func(Generic.HACK).supportShallow()
    def eq(b: Closure): Boolean = func.eq(b.func)
    def apply(seq: Value): Value = func(seq)
    def restrict(dav: Formula.Assignments): Closure = Closure(d => func(Derestricted(d, dav)).restrict(dav))
  }

  object Closure {
    def apply(a: Value): Closure = Closure(_ => a)
  }

  object AbsClosure {
    def apply(a: Value): AbsClosure = AbsClosure(_ => a)
  }

  implicit class AbsClosure(private val func: Formula => Value) extends AnyVal {
    private[Value] def supportShallow(): SupportShallow = func(Formula.Generic.HACK).supportShallow()
    def eq(b: AbsClosure): Boolean = func.eq(b.func)
    def apply(seq: Formula): Value = func(seq)
    def mapd(a: (Value, Formula) => Value): AbsClosure = AbsClosure(d => a(this(d), d))
    def map(a: Value => Value): AbsClosure = AbsClosure(d => a(this(d)))
    def restrict(dav: Formula.Assignments): AbsClosure = AbsClosure(d => func(Formula.Derestricted(d, dav)).restrict(dav))
  }

  type ClosureGraph = Seq[ClosureGraph.Node]
  object ClosureGraph {
    private[Value] def supportShallow(graph: ClosureGraph): SupportShallow = {
      val mss = mutable.ArrayBuffer[Meta]()
      val res = graph.map {
        case IndependentWithMeta(ds, ms, typ) =>
          mss.appendAll(ms)
          typ.supportShallow() ++ (ms.toSet: Set[Referential])
        case DependentWithMeta(ds, mc, c) =>
          val res = c(mss.toSeq, Generic.HACKS)
          mss.appendAll(res._1)
          res._2.supportShallow() ++ (res._1.toSet: Set[Referential])
        case _ => logicError()
      }
      SupportShallow.flatten(res)
    }

    def restrict(graph: ClosureGraph, lv: Formula.Assignments): ClosureGraph =  {
      graph.map {
        case IndependentWithMeta(ds, ms, typ) =>
          IndependentWithMeta(ds, ms, typ.restrict(lv))
        case DependentWithMeta(ds, mc, c) =>
        DependentWithMeta(ds, mc, (a, b) => { val t = c(a, b.map(k => Derestricted(k, lv))); (t._1, t._2.restrict(lv)) })
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
    def referenced: Value

}

  sealed trait Reference extends Referential {
    override def toString: String = "Reference"
    var value: Value
    def referenced = value

  }

  case class Support(names: Set[Long], openMetas: Set[Meta])
  object Support {
    val empty: Support = Support(Set.empty, Set.empty)
  }

  private[Value] case class SupportShallow(names: Set[Long], references: Set[Referential]) {
    def ++(s: SupportShallow) = SupportShallow(names ++ s.names, references ++ s.references)
    def ++(s: Set[Referential]) = SupportShallow(names, references ++ s)
    def +-(s: Set[Long]) = SupportShallow(names ++ s, references)
  }

  object SupportShallow {
    val empty: SupportShallow = SupportShallow(Set.empty, Set.empty)
    def flatten(ss: Seq[SupportShallow]): SupportShallow = SupportShallow(ss.flatMap(_.names).toSet, ss.flatMap(_.references).toSet)
    def orEmpty(a: Option[SupportShallow]): SupportShallow = a.getOrElse(empty)
  }

  sealed trait LocalReferential extends Referential {
    type Self <: LocalReferential
    private var supportCache: Support = null

    private[Value] def supportCached() : Support = {
      if (supportCache != null && supportCache.openMetas.exists(_.isSolved)) {
        supportCache = null
        restrictedCache = null
      }
      supportCache
    }

    override def support(): Support = {
      supportCached() // this will try to invalidate the support cache
      if (supportCache == null) supportCache = super.support()
      supportCache
    }

    // LATER merge the two into one variable??? it is confusing though
    // only not null for parents
    private var restrictedCache: mutable.Map[Formula.Assignments, LocalReferential] = null
    // only not null for children
    private var childRestricted: (LocalReferential, Formula.Assignments) = null
    protected def clearSavedAfterValueChange(): Unit = {
      if (childRestricted != null) logicError() // you don't want to do this
      supportCache = null
      restrictedCache = null
    }

    protected def createNewEmpty(): Self
    protected def restrictAndInitContent(s: Self, assignments: Assignments): Unit
    private[Value] def getRestricted(assigments: Formula.Assignments): Self = {
      if (childRestricted != null) { // direct to parent
        childRestricted._1.asInstanceOf[Referential].getRestricted(childRestricted._2 ++ assigments).asInstanceOf[Self]
      } else {
        val spt = support() // this will re-calculate the support if metas changed
        if (spt.openMetas.nonEmpty) {
          throw ImplementationLimitationCannotRestrictOpenMeta()
        }
        val asgg = assigments.filter(a => spt.names.contains(a._1))
        if (asgg.isEmpty) {
          this.asInstanceOf[Self]
        } else {
          if (restrictedCache == null) restrictedCache = mutable.Map()
          debug(s"getting restricted value by $asgg", 2)
          restrictedCache.get(asgg) match {
            case Some(r) => r.asInstanceOf[Self]
            case None =>
              val n = createNewEmpty()
              n.childRestricted = (this, asgg)
              restrictedCache.put(asgg, n)
              restrictAndInitContent(n, asgg)
              n
          }
        }
      }
    }

    def lookupChildren(v: Referential): Option[Formula.Assignments] = {
      if (this.eq(v)) {
        Some(Set.empty)
      } else {
        assert(childRestricted == null) // you can only lookup children from root
        if (restrictedCache != null) restrictedCache.find(_._2.eq(v)).map(_._1)
        else None
      }
    }
  }

  sealed trait MetaState
  object MetaState {
    case class Closed(v: Value) extends MetaState
    case class Open(id: Long, typ: Value) extends MetaState
  }
  case class Meta(private var _state: MetaState) extends LocalReferential {
    def solved: Value = state.asInstanceOf[MetaState.Closed].v
    def isSolved: Boolean = state.isInstanceOf[MetaState.Closed]
    def state_=(a: MetaState) = {
      clearSavedAfterValueChange()
      _state = a
      if (debug.enabled) assert(isSolved)
    }
    def state = _state

    override type Self = Meta
    override protected def createNewEmpty(): Meta = Meta(null)
    override protected def restrictAndInitContent(s: Meta, assignments: Assignments): Unit = state match {
      case MetaState.Closed(v) => s._state = MetaState.Closed(v.restrict(assignments))
      case MetaState.Open(id, typ) => logicError()
    }

    override def referenced: Value = state match {
      case MetaState.Closed(v) => v
      case MetaState.Open(id, typ) => typ
    }
}


  case class GlobalReference(@lateinit var value: Value) extends Reference {
    override type Self = GlobalReference
    override def getRestricted(asgs: Assignments): GlobalReference = this
    def lookupChildren(v: Referential): Option[Formula.Assignments] = if (this.eq(v)) Some(Set.empty) else None
    override protected private[Value] def supportShallow() = SupportShallow.empty
    override def support(): Support = Support.empty
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

  object Generic {
    private[Value] val HACK = Generic(0, null)
    private[Value] val HACKS = (0 until 20).map(_ => HACK)
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

    override def referenced: Value = _typ
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
        case Unglue(_, m, _) => unapply(m)
        case Transp(typ, _, _) =>
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

  // the reason we must have a domain here is because we support unordered pattern matching
  // LATER is unordered pattern matching really a good thing? but I don't want case trees!
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
    private[Value] def supportShallow(): SupportShallow =  SupportShallow.empty
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
    private[Value] def supportShallow(faces: Seq[Face]): SupportShallow = {
      SupportShallow.flatten(faces.map(f => f.body.supportShallow() +- f.restriction.names))
    }
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

  // create a path from base  => transp, tp is constant on phi
  def transpFill(i: Formula, phi: Formula, tp: AbsClosure, base: Value) =
    Transp(AbsClosure(j => tp(Formula.And(i, j))), Formula.Or(Formula.Neg(i), phi), base)

  // from base => hcomp
  def hfill(tp: Value, base: Value, faces: Seq[Face]) = {
    AbsClosure(i =>
      Hcom(tp, base, faces.map(f => Face(f.restriction, AbsClosure(j => f.body(Formula.And(i, j))))) :+
          Face(Formula.Neg(i), AbsClosure(_ => base)))
    )
  }

  // from base => com
  def fill(tp: AbsClosure, base: Value, faces: Seq[Face]) = {
    AbsClosure(i =>
      Com(AbsClosure(j => tp(Formula.And(i, j))),
        base,
        faces.map(f => Face(f.restriction, AbsClosure(j => f.body(Formula.And(i, j))))) :+
          Face(Formula.Neg(i), AbsClosure(_ => base)))
    )
  }

  // here base is of type tp(1), the result is of type tp(0)
  def transp_inv(phi: Formula, tp: AbsClosure, base: Value) =
    Transp(AbsClosure(j => tp(Formula.Neg(j))), phi, base)

  // here base is of type tp(1), the result is transp_inv(...) => base
  def transpFill_inv(i: Formula, phi: Formula, tp: AbsClosure, base: Value) =
    Transp(AbsClosure(j => tp(Formula.And(Formula.Neg(i), Formula.Neg(j)))), Formula.Or(i, phi), base)

  // where i|- A, u: A(i/r), it's type is A(i/1)
  def forward(A: AbsClosure, r: Formula, u: Value) =
    Transp(AbsClosure(i => A(Formula.Or(i, r))), r, u)

  case class Face(restriction: Formula, body: AbsClosure)
  case class Transp(@stuck_pos tp: AbsClosure, phi: Formula, base: Value) extends Redux {


    override def reduce(): Option[Value] = {
      if (phi.normalForm == Formula.NormalForm.True) {
        Some(base)
      } else {
        tp.apply(Value.Formula.Generic(dgen())).whnf match {
          case _: Function =>
            def tpr(i: Value.Formula) = tp(i).whnf.asInstanceOf[Function]
            Some(Lambda(Closure(v => {
              def w(i: Formula) = transpFill_inv(i, phi, AbsClosure(a => tpr(a).domain), v)
              val w0 = transp_inv(phi, AbsClosure(a => tpr(a).domain), base)
              Transp(AbsClosure(i => tpr(i).codomain(w(i))), phi, App(base, w0))
            })))
          case _: PathType =>
            def tpr(i: Value.Formula) = tp(i).whnf.asInstanceOf[PathType]
            Some(PathLambda(AbsClosure(dim => {
              Com(
                AbsClosure(i => tpr(i).typ(dim)),
                PathApp(base, dim),
                Seq(
                  Face(phi, AbsClosure(_ => PathApp(base, dim))),
                  Face(Formula.Neg(dim), AbsClosure(a => tpr(a).left)),
                  Face(dim, AbsClosure(a => tpr(a).right))
                ))
            })))
          case r: Record =>
            if (r.nodes.isEmpty) {
              Some(base)
            } else {
              def tpr(i: Value.Formula) = tp(i).whnf.asInstanceOf[Record]
              val closures = mutable.ArrayBuffer[AbsClosure]()
              for (i <- r.nodes.indices) {
                val res = r.nodes(i) match {
                  case _: ClosureGraph.Independent =>
                    AbsClosure(j => {
                      transpFill(j,
                        phi,
                        AbsClosure(k => tpr(k).nodes(i).independent.typ),
                        Projection(base, i)
                      )
                    })
                  case _: ClosureGraph.Dependent =>
                    AbsClosure(j => {
                      transpFill(j,
                        phi,
                        AbsClosure(k => {val tt = tpr(k); ClosureGraph.get(tt.nodes, i, j => closures(j)(k))  }),
                        Projection(base, i)
                      )
                    })
                }
                closures.append(res)
              }
              Some(Make(closures.toSeq.map(_.apply(Formula.True))))
            }
          case _: Sum =>
            ???
          case _: Universe =>
            Some(base)
          case _: Internal => logicError()
          case _ => None
        }
      }
    }
  }
  case class Com(@stuck_pos tp: AbsClosure, base: Value, faces: Seq[Face]) extends Redux {
    override def reduce(): Option[Value] =
      Some(Hcom(
        tp(Formula.True),
        forward(tp, Formula.False, base),
        faces.map(f => Face(f.restriction, AbsClosure(i => forward(tp, i, f.body(i)))))))
  }

  case class Hcom(@stuck_pos tp: Value, base: Value, faces: Seq[Face]) extends Redux {
    override def reduce(): Option[Value] = {
      faces.find(_.restriction.normalForm == NormalForm.True) match {
        case Some(t) => Some(t.body(Formula.True))
        case None =>
          val tp0 = tp.whnf
           tp0 match {
            case PathType(a, u, w) =>
               Some(PathLambda(AbsClosure(j => Hcom(a(j), PathApp(base, j), Seq(
                 Face(Formula.Neg(j), AbsClosure(_ => u)),
                 Face(j, AbsClosure(_ => w))
               )))))
            case Function(_, _, b) =>
               Some(Lambda(Closure(v => Hcom(b(v), App(base, v), faces.map(f => Face(f.restriction, f.body.map(j => App(j, v))))))))
            case Record(i, ns, ms, cs) =>
              if (cs.isEmpty) {
                Some(base)
              } else {
                val closures = mutable.ArrayBuffer[AbsClosure]()
                for (i <- cs.indices) {
                  val res = cs(i) match {
                    case in: ClosureGraph.Independent =>
                      hfill(in.typ, Projection(base, i),
                        faces.map(f => Face(f.restriction, f.body.map(a => Projection(a, i))))
                      )
                    case com: ClosureGraph.Dependent =>
                      fill(
                        AbsClosure(k => ClosureGraph.get(cs, i, j => closures(j)(k))),
                        Projection(base, i),
                        faces.map(n => Face(n.restriction, n.body.map(a => Projection(a, i))))
                      )
                  }
                  closures.append(res)
                }
                Some(Make(closures.toSeq.map(_.apply(Formula.True))))
              }
            case u: Universe => ???
            case Sum(i, cs) => ???
            case _: Internal => logicError()
            case _ => None
          }
      }
    }
  }

  case class GlueType(ty: Value, @stuck_pos faces: Seq[Face]) extends CubicalUnstable
  case class Glue(m: Value, @stuck_pos faces: Seq[Face]) extends CubicalUnstable
  case class Unglue(ty: Value, base: Value, @stuck_pos faces: Seq[Face]) extends Redux {
    override def reduce(): Option[Value] = ???
  }
}


sealed trait Value {
  final override def equals(obj: Any): Boolean = (this, obj) match {
    case (r: Referential, j: Referential) => r.eq(j)
    case _ => logicError()
  }


  override def hashCode(): Int = this match {
    case r: Referential => super.hashCode()
    case _ => logicError()
  }

  private[Value] var _from: Value = _
  private[Value] var _whnfCache: Object = _

  def fromOrThis: Value = if (_from == null) this else _from

  // it is ensured that if the value is not reducable, it will return the same reference
  def whnf: Value = {
    def eqFaces(f1: Seq[Face], f2: Seq[Face]): Boolean = f1.eq(f2) || (f1.size == f2.size && f1.zip(f2).forall(p => {
      p._1.restriction == p._2.restriction && p._1.body.eq(p._2.body)
    }))
    val cached =
      if (_whnfCache == null) {
        null
      } else {
        _whnfCache match {
          case (v: Value, m: Meta) =>
            if (m.isSolved) {
              _whnfCache = null
              null
            } else {
              v
            }
          case v: Value =>
            v
        }
      }
    if (cached == null) {
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
        case GlueType(tm, faces) =>
          faces.find(_.restriction.normalForm == Formula.NormalForm.True).map(b => Projection(b.body(Formula.Generic.HACK), 0).whnf).getOrElse(this)
        case Glue(base, faces) =>
          faces.find(_.restriction.normalForm == Formula.NormalForm.True).map(_.body(Formula.Generic.HACK).whnf).getOrElse(this)
        case Unglue(x, m, f) =>
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
      val cache = candidate match {
        case Value.WhnfOpenMetaHeaded(m) =>
          (candidate, m)
        case _ =>
          candidate
          // remember for stable values
      }
      _whnfCache = cache
      candidate._whnfCache = cache
      candidate
    } else {
      cached
    }
  }


  def support(): Support = {
    val tested = mutable.Set.empty[Referential]
    val ss = supportShallow() // in case of reference, it will just put the reference here
    val toTest = mutable.Set.from(ss.references)
    val names = mutable.Set.from(ss.names)
    while (toTest.nonEmpty) {
      val candidate = toTest.head
      toTest.remove(candidate)
      candidate match {
        case GlobalReference(value) => // skip global reference
        case Generic(id, _typ) if id == 0 => // skip hack generic
        case r: LocalReferential =>
          tested.add(candidate)
          val cached = r.supportCached()
          if (cached != null) {
            names.addAll(cached.names)
            tested.addAll(cached.openMetas)
          } else {
            val SupportShallow(ns, rs) = candidate.referenced.supportShallow()
            names.addAll(ns)
            toTest.addAll(rs.filter(tested))
          }
      }
    }
    val spt = Support(names.toSet, tested.flatMap {
      case m@Meta(o: MetaState.Open) => Some(m)
      case _ => None
    }.toSet)
    if (spt.names.nonEmpty) debug(s"non-empty support ${spt.names}", 2)
    spt
  }

  private[Value] def supportShallow(): SupportShallow  = this match {
    case Universe(level) => SupportShallow.empty
    case Function(domain, impict, codomain) => domain.supportShallow() ++ codomain.supportShallow()
    case Lambda(closure) => closure.supportShallow()
    case PatternLambda(id, domain, typ, cases) =>
      domain.supportShallow() ++ typ.supportShallow() ++ SupportShallow.flatten(cases.map(_.closure.supportShallow()))
    case Record(inductively, names, ims, nodes) =>
      SupportShallow.orEmpty(inductively.map(_.supportShallow())) ++ ClosureGraph.supportShallow(nodes)
    case Make(values) => SupportShallow.flatten(values.map(_.supportShallow()))
    case Construct(name, vs) =>
      SupportShallow.flatten(vs.map(_.supportShallow()))
    case Sum(inductively, constructors) =>
      SupportShallow.orEmpty(inductively.map(_.supportShallow())) ++ SupportShallow.flatten(constructors.map(a => ClosureGraph.supportShallow(a.nodes)))
    case PathType(typ, left, right) =>
      typ.supportShallow() ++ left.supportShallow() ++ right.supportShallow()
    case PathLambda(body) => body.supportShallow()
    case App(lambda, argument) => lambda.supportShallow() ++ argument.supportShallow()
    case PatternRedux(lambda, stuck) => lambda.supportShallow() ++ stuck.supportShallow()
    case Projection(make, field) => make.supportShallow()
    case PathApp(left, dimension) => left.supportShallow() +- dimension.names
    case Transp(tp, direction, base) => tp.supportShallow() ++ base.supportShallow() +- direction.names
    case Com(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ Face.supportShallow(faces)
    case Hcom(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ Face.supportShallow(faces)
    case Maker(value, field) => value.supportShallow()
    case GlueType(tp, faces) => tp.supportShallow()++ Face.supportShallow(faces)
    case Glue(base, faces) => base.supportShallow() ++ Face.supportShallow(faces)
    case Unglue(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ Face.supportShallow(faces)
    case referential: Referential => SupportShallow.empty ++ Set(referential)
    case internal: Internal => logicError()
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
    case Transp(tp, direction, base) =>
      Transp(tp.restrict(lv), direction.restrict(lv), base.restrict(lv))
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
    case Glue(base, faces) =>
      Glue(base.restrict(lv), Face.restrict(faces, lv))
    case Glue(base, faces) =>
      Glue(base.restrict(lv), Face.restrict(faces, lv))
    case Unglue(tp, base, faces) =>
      Unglue(tp.restrict(lv), base.restrict(lv), Face.restrict(faces, lv))
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
  private[Value] def infer: Value = {
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
      case GlueType(ty, pos) =>
        ty.infer // FIXME this seems wrong, what if we annotate the level? generally we want to make sure this is working as intent
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
  var equiv_of: Value = null
}
