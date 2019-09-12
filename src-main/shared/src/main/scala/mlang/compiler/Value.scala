package mlang.compiler

import mlang.compiler.LongGen.Negative.{dgen, gen}
import mlang.compiler.Value.Formula.{Assignments, NormalForm}
import mlang.compiler.Value.{AbsClosure, _}
import mlang.utils.{Name, debug}

import scala.annotation.Annotation
import scala.collection.mutable

private[compiler] class stuck_pos extends Annotation
private[compiler] class type_annotation extends Annotation // see Readme about abstract-surface syntax mismatch

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

    def normalFormTrue = normalForm == NormalForm.True

    def normalForm: NormalForm  = {
      def merge(a: NormalForm, b: NormalForm): NormalForm = {
        def properSupersetOfAny(c: Assignments, g: NormalForm) = g.exists(g => g.subsetOf(c) && g != c)
        a.filter(c => !properSupersetOfAny(c, b)) ++ b.filter(c => !properSupersetOfAny(c, a))
      }
      this match {
        case True => NormalForm.True
        case False => NormalForm.False
        case Formula.Generic(id) => Set(Set((id, true)))
        case And(left, right) =>
          val ln = left.normalForm.toSeq
          val rn = right.normalForm.toSeq
          ln.flatMap(i => rn.map(r => Set(i ++ r) : NormalForm)).foldLeft(NormalForm.False) { (a, b) => merge(a, b) }
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

    def fswap(w: Long, z: Formula): Formula = this match {
      case g:Formula.Generic => if (g.id == w) z else g
      case Formula.True => Formula.True
      case Formula.False => Formula.False
      case And(left, right) => And(left.fswap(w, z), right.fswap(w, z))
      case Or(left, right) => Or(left.fswap(w, z), right.fswap(w, z))
      case Neg(unit) => Neg(unit.fswap(w, z))
      case _: Formula.Internal => logicError()
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
    def apply(nf: NormalForm): Formula =
      nf.foldLeft(Formula.False : Formula) {(f, z) =>
        Formula.Or(f, z.foldLeft(Formula.True : Formula) { (t, y) => Formula.And(t, if (y._2) Formula.Generic(y._1) else Formula.Neg(Formula.Generic(y._1)))})}

    def elim(f: Formula, i: Long): Formula = Formula(NormalForm.elim(f.normalForm, i))


    def phi(se: Seq[Formula]) = se.flatMap(_.normalForm).toSet
    type Assignment = (Long, Boolean)
    type Assignments = Set[Assignment]
    object Assignments {
      def satisfiable(rs: Assignments): Boolean = rs.map(_._1).size == rs.size
    }
    type NormalForm = Set[Assignments]
    object NormalForm {
      def elim(nf: NormalForm, value: Long) = nf.filter(!_.exists(_._1 == value))

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
    object Or {
      def apply(fs: Seq[Formula]): Formula = {
        fs.foldLeft(Formula.False: Formula) {
          (f, a) => Or(f, a)
        }
      }
    }
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
    def fswap(w: Long, z: Formula): MultiClosure = MultiClosure(d => func(d).fswap(w, z))
  }

  implicit class Closure(private val func: Value => Value) extends AnyVal {
    private[Value] def supportShallow(): SupportShallow = func(Generic.HACK).supportShallow()
    def eq(b: Closure): Boolean = func.eq(b.func)
    def apply(seq: Value): Value = func(seq)
    def restrict(dav: Formula.Assignments): Closure = Closure(d => func(Derestricted(d, dav)).restrict(dav))
    def fswap(w: Long, z: Formula): Closure = Closure(d => func(d).fswap(w, z))
  }

  object Closure {
    def apply(a: Value): Closure = Closure(_ => a)
  }

  object AbsClosure {
    def apply(a: Value): AbsClosure = AbsClosure(_ => a)
  }

  // LATER make sure AnyVal classes is eliminated in bytecode
  implicit class AbsClosure(private val func: Formula => Value) extends AnyVal {
    private[Value] def supportShallow(): SupportShallow = func(Formula.Generic.HACK).supportShallow()
    def eq(b: AbsClosure): Boolean = func.eq(b.func)
    def apply(seq: Formula): Value = func(seq)
    def mapd(a: (Value, Formula) => Value): AbsClosure = AbsClosure(d => a(this(d), d))
    def map(a: Value => Value): AbsClosure = AbsClosure(d => a(this(d)))
    def restrict(dav: Formula.Assignments): AbsClosure = AbsClosure(d => func(Formula.Derestricted(d, dav)).restrict(dav))
    def fswap(w: Long, z: Formula): AbsClosure = AbsClosure(d => func(d).fswap(w, z))
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

    def fswap(graph: ClosureGraph, w: Long, z: Formula): ClosureGraph = {
      graph.map {
        case IndependentWithMeta(ds, ms, typ) =>
          IndependentWithMeta(ds, ms, typ.fswap(w, z))
        case DependentWithMeta(ds, mc, c) =>
          DependentWithMeta(ds, mc, (a, b) => {
            val t = c(a, b); (t._1.map(_.fswap(w, z).asInstanceOf[Value.Meta]), t._2.fswap(w, z)) })
        case _ => logicError()
      }
    }
    def restrict(graph: ClosureGraph, lv: Formula.Assignments): ClosureGraph =  {
      graph.map {
        case IndependentWithMeta(ds, ms, typ) =>
          IndependentWithMeta(ds, ms, typ.restrict(lv))
        case DependentWithMeta(ds, mc, c) =>
        DependentWithMeta(ds, mc, (a, b) => {
          val t = c(a, b.map(k => Derestricted(k, lv))); (t._1.map(_.restrict(lv).asInstanceOf[Value.Meta]), t._2.restrict(lv)) })
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
  sealed trait Canonical extends Value
  sealed trait CubicalUnstableCanonical extends Value // this value can reduce more, but only when restricted
  sealed trait Redux extends Value {
    // TODO this is not that well defined, since some term will always whnf on arguments, some not
    // maybe inline in whnf
    def reduce(): Option[Value]

    def reduceThenWhnfOrSelf() = reduce() match {
      case Some(r) => r.whnf
      case _ => this
    }
  }

  case class Derestricted(a: Value, asgn: Formula.Assignments) extends Internal

  sealed trait Referential extends Value {
    _from = this
    type Self <: Referential
    private[Value] def getRestrict(asgs: Formula.Assignments): Self
    private[Value] def getFswap(w: Long, z: Formula): Self
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
    private var fswapCache: mutable.Map[(Long, Formula), LocalReferential] = null
    protected def clearSavedAfterValueChange(): Unit = {
      if (childRestricted != null) logicError() // you don't want to do this
      supportCache = null
      restrictedCache = null
    }

    protected def createNewEmpty(): Self
    protected def restrictAndInitContent(s: Self, assignments: Assignments): Unit
    protected def fswapAndInitContent(s: Self, w: Long, z: Formula): Unit

    private[Value] def getFswap(w: Long, z: Formula): Self = {
      val spt = support()
      if (spt.openMetas.nonEmpty) {
        throw ImplementationLimitationCannotRestrictOpenMeta()
      }
      if (!spt.names.contains(w)) {
        this.asInstanceOf[Self]
      } else {
        if (fswapCache == null) fswapCache = mutable.Map()
        debug(s"getting fswap value by $w, $z", 2)
        val key = (w, z)
        fswapCache.get(key) match {
          case Some(r) => r.asInstanceOf[Self]
          case None =>
            val n = createNewEmpty()
            n.supportCache = Support(spt.names -- Set(w) ++ z.names, spt.openMetas)
            fswapCache.put(key, n)
            fswapAndInitContent(n, w, z)
            n
        }
      }
    }

    private[Value] def getRestrict(assigments: Formula.Assignments): Self = {
      if (childRestricted != null) { // direct to parent
        childRestricted._1.asInstanceOf[Referential].getRestrict(childRestricted._2 ++ assigments).asInstanceOf[Self]
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
              n.supportCache = Support(spt.names -- asgg.map(_._1), spt.openMetas)
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
    case class Open(id: Long, @type_annotation typ: Value) extends MetaState
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
      case _: MetaState.Open => logicError()
    }
    override protected def fswapAndInitContent(s: Meta, w: Long, z: Formula): Unit = state match {
      case MetaState.Closed(v) => s._state = MetaState.Closed(v.fswap(w, z))
      case _: MetaState.Open => logicError()
    }

    override def referenced: Value = state match {
      case MetaState.Closed(v) => v
      case MetaState.Open(id, typ) => typ
    }
}


  case class GlobalReference(@lateinit var value: Value) extends Reference {
    override type Self = GlobalReference
    override private[Value] def getRestrict(asgs: Assignments): GlobalReference = this
    private[Value] def getFswap(w: Long, z: Formula): Self = this
    def lookupChildren(v: Referential): Option[Formula.Assignments] = if (this.eq(v)) Some(Set.empty) else None
    override protected def supportShallow(): SupportShallow = SupportShallow.empty
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

    override protected def fswapAndInitContent(s: LocalReference, w: Long, z: Formula) =
      s._value = value.fswap(w, z)
  }

  object Generic {
    private[Value] val HACK = Generic(0, null)
    private[Value] val HACKS = (0 until 20).map(_ => HACK)
  }
  case class Generic(id: Long, @type_annotation @lateinit private var _typ: Value) extends LocalReferential {

    def typ_=(a: Value) = {
      clearSavedAfterValueChange()
      _typ = a
    }
    def typ = _typ

    override type Self = Generic
    override protected def createNewEmpty(): Generic = Generic(id, null)
    override protected def restrictAndInitContent(s: Generic, assignments: Assignments) =
      s._typ = typ.restrict(assignments)

    override protected def fswapAndInitContent(s: Generic, w: Long, z: Formula) =
      logicError() // currently we only use fresh variable, and fresh variable should not generate new generic supported

    override def referenced: Value = _typ
}

  object WhnfStuckReason {

    def unapply(value: Value): Option[Value] = {
      value match {
        case _: Canonical => None
        case _: CubicalUnstableCanonical => None
        case _: Generic => None
        case o: Meta => Some(o)
        case App(lambda, _) => unapply(lambda)
        case Projection(make, _) => unapply(make)
        case a@PatternRedux(_, stuck) =>
          stuck match {
            case c: Canonical => Some(a) // can only be make or construct
            case _ => unapply(stuck)
          }
        case PathApp(left, _) => unapply(left)
        case t@Transp(typ, _, _) =>
          // TODO this rule is really wired...
          unapply(typ(Formula.Generic(dgen())).whnf).map {
            case m: Meta => m
            case _ => t
          }
        case Hcomp(tp, _, _) => unapply(tp)
        case u@Unglue(_, m, _) => Some(u)
        case _: Comp => logicError()
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


  case class Universe(level: Int) extends Canonical

  object Universe {
    val TypeInType = true
    def suc(i: Int) = Universe(if (TypeInType) 0 else i)
    def level0 = Universe(0)
    def level1 = Universe(if (TypeInType) 0 else 1)
  }

  case class Function(domain: Value, impict: Boolean, codomain: Closure) extends Canonical

  /**
    * whnf: lambda is whnf and is not a canonical
    */
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
  case class Lambda(closure: Closure) extends Canonical
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
  // so pattern redux can be stuck value when non of their arguments is stuck
  // LATER is unordered pattern matching really a good thing? but I don't want case trees!
  case class PatternLambda(id: Long, @type_annotation domain: Value, @type_annotation typ: Closure, cases: Seq[Case]) extends Canonical

  /**
    * whnf: stuck is whnf AND pattern redux cannot continue
    */
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
    def fswap(w: Long, z: Formula): Inductively = this
    private[Value] def supportShallow(): SupportShallow =  SupportShallow.empty
  }

  case class Record(
      inductively: Option[Inductively],
      names: Seq[Name],
      ims: Seq[Boolean],
      nodes: ClosureGraph) extends Canonical {
    assert(names.size == nodes.size)

    private def rthis(): Value = LocalReference(this)

    private lazy val makerAndType: (Value, Value) = ClosureGraph.makerAndType(nodes, ims, vs => Make(vs), rthis())
    lazy val maker: Value = makerAndType._1
    lazy val makerType: Value = makerAndType._2

    def projectedType(values: Value, name: Int): Value = {
      ClosureGraph.get(nodes, name, i => Projection(values, i))
    }
  }
  case class Make(values: Seq[Value]) extends Canonical
  // FIXME do away with this
  case class Maker(value: Value, field: Int) extends Value

  /**
    * whnf: make is whnf and is not canonical
    */
  case class Projection(@stuck_pos make: Value, field: Int) extends Redux {
    def reduce(): Option[Value] = {
      make match {
        case Make(vs) => Some(vs(field))
        case _ => None
      }
    }
  }

  case class Construct(name: Int, vs: Seq[Value]) extends Canonical
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
      constructors: Seq[Constructor]) extends Canonical {
    for (c <- constructors) {
      c._sum = this
    }
  }

  case class PathType(typ: AbsClosure, left: Value, right: Value) extends Canonical
  case class PathLambda(body: AbsClosure) extends Canonical

  /**
    * whnf: left is whnf but not canonical, and dimension is not constant
    */
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

  type System[T] = Map[Formula, T]
  case class Face(restriction: Formula, body: AbsClosure)
  object Face {
    private[Value] def supportShallow(faces: Seq[Face]): SupportShallow = {
      SupportShallow.flatten(faces.map(f => f.body.supportShallow() +- f.restriction.names))
    }
    def fswap(faces: Seq[Face], w: Long, z: Formula): Seq[Face] = {
      faces.flatMap(n => {
        val r = n.restriction.fswap(w, z)
        // TODO can you simply remove unsatifiable faces?
        if (r.normalForm == Formula.NormalForm.False) {
          None
        } else {
          Some(Face(r, n.body.fswap(w, z)))
        }
      })
    }
    def restrict(faces: Seq[Face], lv: Formula.Assignments) = {
      faces.flatMap(n => {
        val r = n.restriction.restrict(lv)
        // TODO can you simply remove unsatifiable faces?
        if (r.normalForm == Formula.NormalForm.False) {
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
      Hcomp(tp, base, faces.map(f => Face(f.restriction, AbsClosure(j => f.body(Formula.And(i, j))))) :+
          Face(Formula.Neg(i), AbsClosure(_ => base)))
    )
  }

  // from base => com
  def fill(tp: AbsClosure, base: Value, faces: Seq[Face]) = {
    AbsClosure(i =>
      Comp(AbsClosure(j => tp(Formula.And(i, j))),
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

  /**
    * whnf: tp on a generic value cannot reduce to a canonical
    */
  case class Transp(@stuck_pos tp: AbsClosure, phi: Formula, base: Value) extends Redux {


    override def reduce(): Option[Value] = {
      if (phi.normalFormTrue) {
        Some(base)
      } else {
        val dim = dgen()
        tp.apply(Value.Formula.Generic(dim)).whnf match {
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
              Comp(
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
          case g: GlueType =>
            Some(transpGlue(g, dim, phi, base))
          case _: Universe =>
            Some(base)
          case _: Internal => logicError()
          case _ => None
        }
      }
    }
  }

  def transpGlue(B: GlueType, dim: Long, si: Formula, u0: Value): Value = {
    def B_swap(f: Formula) = B.fswap(dim, f).asInstanceOf[GlueType]
    val B0 = B_swap(Formula.False)
    def A(i: Formula) = B.ty.fswap(dim, i)
    val B1 = B_swap(Formula.True)
    val phi1 = Formula.Or(B1.faces.map(_.restriction))
    val A1 = B1.ty
    val A0 = B0.ty
    // a0: A(i/0)
    val a0 = LocalReference(Unglue(A0, u0, B0.faces))
    val phi_elim_i = Formula.elim(Formula.Or(B.faces.map(_.restriction)), dim)
    // defined in phi_elim_i
    def t_tide(trueFace: Value, i: Formula) = {
      transpFill(i, si, AbsClosure(i => {
      Projection(trueFace.fswap(dim, i), 0)
      }), u0)
    }
    def trueElimFace() = B.faces.find(b => Formula.elim(b.restriction, dim).normalFormTrue).get.body(Formula.Generic.HACK)
    def t1(trueFace: Value) = t_tide(trueFace, Formula.True)
    // a1: A(i/1) and is defined on both si and elim(i, phi)
    val a1 = LocalReference(Comp(
      AbsClosure(i => A(i)),
      a0,
      Seq(
        Face(si, AbsClosure(_ => a0)),
        Face(phi_elim_i, AbsClosure(i => {
          val tf = trueElimFace()
          val EQi  = tf.fswap(dim, i)
          val w = Projection(EQi, 1)
          App(Projection(w, 0), t_tide(tf, i))
        }))
      )))
    // ..., phi(i/1) |- (t1`, alpha) // true face must have (i/1)
    def pair(trueFace: Value) = {
      val w = Projection(trueFace, 1)
      val compo = App(Projection(w, 1), a1) // is_contractible(fiber_at(w(i/1).1, a1))
      Comp(AbsClosure(i => A(i)), Projection(compo, 0),
        Seq(
          Face(si, AbsClosure(i => {
            val u = Make(Seq(u0, PathLambda(AbsClosure(_ => a1))))
            PathApp(App(Projection(compo, 1), u), i)
          })),
          Face(phi_elim_i, AbsClosure(i => {
            val u = Make(Seq(t1(trueElimFace()), PathLambda(AbsClosure(_ => a1))))
            PathApp(App(Projection(compo, 1), u), i)
          }))
        )
      )
    }
    val a1p = Hcomp(A1, a1,
      Seq(
        Face(phi1, AbsClosure(j => {
          val bd = B1.faces.find(_.restriction.normalFormTrue).get.body(Formula.Generic.HACK)
          PathApp(Projection(pair(bd), 1), j)
        })),
        Face(si, AbsClosure(j => a1))))
    Glue(a1p, Seq(Face(phi1, AbsClosure(_ => {
      val bd = B1.faces.find(_.restriction.normalFormTrue).get.body(Formula.Generic.HACK)
      Projection(pair(bd), 0)
    }))))
  }

  def hcompGlue(B: GlueType, u0: Value, faces: Seq[Face]): Value = {
    val si = Formula.Or(faces.map(_.restriction))
    def t_tide(trueFace: Value) = {
      hfill(Projection(trueFace, 0), u0, faces)
    }
    def t1(trueFace: Value) = t_tide(trueFace)(Formula.True)
    val a1 = Hcomp(B.ty, Unglue(B.ty, u0, faces),
      faces.map(f => Face(f.restriction, f.body.map(u => Unglue(B.ty, u, B.faces)))) ++
      B.faces.map(f => Face(f.restriction, f.body.mapd((pair, i) => {
        val w = Projection(pair, 1)
        val f = Projection(w, 0)
        App(f, t_tide(pair)(i))
      })))
    )
    Glue(a1, B.faces.map(f => Face(f.restriction, f.body.map(bd => t1(bd)))))
  }


  // TODO when we have a syntax for partial values, these should be removed
  case class Comp(@stuck_pos tp: AbsClosure, base: Value, faces: Seq[Face]) extends Redux {
    override def reduce(): Option[Value] =
      Some(Hcomp(
        tp(Formula.True),
        forward(tp, Formula.False, base),
        faces.map(f => Face(f.restriction, AbsClosure(i => forward(tp, i, f.body(i)))))))
  }

  /**
    * whnf: tp is whnf and not canonical
    */
  case class Hcomp(@type_annotation @stuck_pos tp: Value, base: Value, faces: Seq[Face]) extends Redux {


    override def reduce(): Option[Value] = {
      faces.find(_.restriction.normalFormTrue) match {
        case Some(t) => Some(t.body(Formula.True))
        case None =>
          val tp0 = tp.whnf
           tp0 match {
            case PathType(a, u, w) =>
               Some(PathLambda(AbsClosure(j => Hcomp(a(j), PathApp(base, j), Seq(
                 Face(Formula.Neg(j), AbsClosure(_ => u)),
                 Face(j, AbsClosure(_ => w))
               )))))
            case Function(_, _, b) =>
               Some(Lambda(Closure(v => Hcomp(b(v), App(base, v), faces.map(f => Face(f.restriction, f.body.map(j => App(j, v))))))))
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
            case u: Universe =>
              val res = Glue(tp, faces.map(f =>
                Face(f.restriction, AbsClosure(_ => {
                  val A = f.body(Formula.False)
                  val B = f.body(Formula.True)
                  Make(Seq(B, Apps(BuiltIn.path_to_equiv, Seq(B, A, PathLambda(AbsClosure(a => f.body(Formula.Neg(a))))))))
                }))))
              Some(res)
            case Sum(i, cs) => ???
            case g: Glue =>
              Some(hcompGlue(g, base, faces))
            case _: Internal => logicError()
            case _ => None
          }
      }
    }
  }

  /**
    * whnf: faces is not constant
    */
  case class GlueType(ty: Value, @stuck_pos faces: Seq[Face]) extends CubicalUnstableCanonical
  /**
    * whnf: faces is not constant
    */
  case class Glue(m: Value, @stuck_pos faces: Seq[Face]) extends CubicalUnstableCanonical
  /**
    * whnf: faces is not constant, base is whnf, and m's whnf is not glue
    * LATER this is how the whnf is defined, so glue is considered canonical
    */
  case class Unglue(ty: Value, base: Value, @stuck_pos faces: Seq[Face]) extends Redux {
    override def reduce(): Option[Value] = logicError() // in whnf
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
          case (v: Value, m: Value) =>
            m match {
              case m: Meta =>
                if (m.isSolved) {
                  _whnfCache = null
                  null
                } else {
                  v
                }
              case o =>
                if (o.eq(this)) {
                  _whnfCache = null
                  null
                } else {
                  if (!o.whnf.eq(o)) {
                    _whnfCache = null
                    null
                  } else {
                    v
                  }
                }
            }
          case v: Value =>
            v
        }
      }
    if (cached == null) {
      val candidate = this match {
        case a: Canonical =>
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
          // TODO don't do this equals stuff!!!
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
        case com@Comp(tp, base, faces) =>
          com.reduceThenWhnfOrSelf() match {
            case Comp(t2, b2, f2) if tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
            case a => a
          }
        case hcom@Hcomp(tp, base, faces) =>
          Hcomp(tp.whnf, base, faces).reduceThenWhnfOrSelf() match {
            case Hcomp(t2, b2, f2) if tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
            case a => a
          }
        case GlueType(tm, faces) =>
          faces.find(_.restriction.normalFormTrue).map(b => Projection(b.body(Formula.Generic.HACK), 0).whnf).getOrElse(this)
        case Glue(base, faces) =>
          faces.find(_.restriction.normalFormTrue).map(_.body(Formula.Generic.HACK).whnf).getOrElse(this)
        case Unglue(ty, base, faces) =>
          val red = faces.find(_.restriction.normalFormTrue).map(b => App(Projection(b.body(Formula.Generic.HACK), 1), base).whnf)
          red match {
            case Some(a) => a
            case None =>
              val bf = base.whnf
              bf match {
              case Glue(b, _) => b.whnf
              case _ => if (bf.eq(base)) this else Unglue(ty, bf, faces)
            }
          }
        case _: Internal =>
          logicError()
      }
      // because some values is shared, it means the solved ones is not created for this whnf, we don't say this
      // is from us
      // TODO these are already defined ones, think more about this
      if (!candidate.eq(candidate._from)) {
        if (!candidate.eq(this)) {
          candidate._from = this
        }
      }
      val cache = candidate match {
        // LATER I'm surprised that this thing is so tricky. maybe remove this (and the equals stuff)
        case Value.WhnfStuckReason(m) =>
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


  // FIXME current problems of restriction/fswap system:
  // they have overlapping, fswap by constant is similar to restriction, but they produce
  // referential different terms (this is not a bug, but is a dirtyness)
  // newly produced local referenctal has the problem that they will not be compared by reference
  // easily, (again, not a bug, only dirtyness)
  // but I think we can currently
  // without fswap, the first problem dispears
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
          tested.add(r)
          val cached = r.supportCached()
          if (cached != null) {
            names.addAll(cached.names)
            tested.addAll(cached.openMetas)
          } else {
            val SupportShallow(ns, rs) = candidate.referenced.supportShallow()
            names.addAll(ns)
            toTest.addAll(rs.filterNot(tested))
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

  protected def supportShallow(): SupportShallow  = this match {
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
    case Comp(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ Face.supportShallow(faces)
    case Hcomp(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ Face.supportShallow(faces)
    case Maker(value, field) => value.supportShallow()
    case GlueType(tp, faces) => tp.supportShallow()++ Face.supportShallow(faces)
    case Glue(base, faces) => base.supportShallow() ++ Face.supportShallow(faces)
    case Unglue(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ Face.supportShallow(faces)
    case referential: Referential => SupportShallow.empty ++ Set(referential)
    case internal: Internal => logicError()
  }

  /**
    * fresh swap, the id being swapped cannot be used after. this helps because no need for Deswap...
    */
  def fswap(w: Long, z: Formula): Value = this match {
    case u: Universe => u
    case Function(domain, im, codomain) => Function(domain.fswap(w, z), im, codomain.fswap(w, z))
    case Record(inductively, ms, ns, nodes) =>
      Record(inductively.map(_.fswap(w, z)), ms, ns, ClosureGraph.fswap(nodes, w, z))
    case Make(values) => Make(values.map(_.fswap(w, z)))
    case Construct(name, vs) => Construct(name, vs.map(_.fswap(w, z)))
    case Sum(inductively, constructors) =>
      Sum(inductively.map(_.fswap(w, z)), constructors.map(n => Constructor(n.name, n.ims, ClosureGraph.fswap(n.nodes, w, z))))
    case Lambda(closure) => Lambda(closure.fswap(w, z))
    case PatternLambda(id, dom, typ, cases) =>
      PatternLambda(id, dom.fswap(w, z), typ.fswap(w, z), cases.map(a => Case(a.pattern, a.closure.fswap(w, z))))
    case PathType(typ, left, right) =>
      PathType(typ.fswap(w, z), left.fswap(w, z), right.fswap(w, z))
    case PathLambda(body) => PathLambda(body.fswap(w, z))
    case App(lambda, argument) => App(lambda.fswap(w, z), argument.fswap(w, z))
    case Transp(tp, direction, base) => Transp(tp.fswap(w, z), direction.fswap(w, z), base.fswap(w, z))
    case Hcomp(tp, base, faces) => Hcomp(tp.fswap(w, z), base.fswap(w, z), Face.fswap(faces, w, z))
    case Comp(tp, base, faces) => Comp(tp.fswap(w, z), base.fswap(w, z), Face.fswap(faces, w, z))
    case Maker(value, field) => Maker(value.fswap(w, z), field)
    case Projection(make, field) => Projection(make.fswap(w, z), field)
    case PatternRedux(lambda, stuck) =>
      PatternRedux(lambda.fswap(w, z).asInstanceOf[PatternLambda], stuck.fswap(w, z))
    case PathApp(left, stuck) => PathApp(left.fswap(w, z), stuck.fswap(w, z))
    case GlueType(base, faces) => GlueType(base.fswap(w, z), Face.fswap(faces, w, z))
    case Glue(base, faces) => Glue(base.fswap(w, z), Face.fswap(faces, w, z))
    case Unglue(tp, base, faces) => Unglue(tp.fswap(w, z), base.fswap(w, z), Face.fswap(faces, w, z))
    case g: Referential => g.getFswap(w, z)
    case _: Internal => logicError()
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
    case Hcomp(tp, base, faces) =>
      Hcomp(tp.restrict(lv), base.restrict(lv), Face.restrict(faces, lv))
    case Comp(tp, base, faces) =>
      Comp(tp.restrict(lv), base.restrict(lv), Face.restrict(faces, lv))
    case Maker(value, field) =>
      Maker(value.restrict(lv), field)
    case Projection(make, field) =>
      Projection(make.restrict(lv), field)
    case PatternRedux(lambda, stuck) =>
      PatternRedux(lambda.restrict(lv).asInstanceOf[PatternLambda], stuck.restrict(lv))
    case PathApp(left, stuck) =>
      PathApp(left.restrict(lv), stuck.restrict(lv))
    case GlueType(base, faces) =>
      GlueType(base.restrict(lv), Face.restrict(faces, lv))
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
      g.getRestrict(lv)
  }


  // TODO as said bellow, infer on value can be probmatic, so maybe we should disable this functionality
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
      case h: Hcomp => h.tp
      case t: Transp => t.tp(Formula.True)
      case h: Comp => h.tp(Formula.True)
      case GlueType(ty, pos) =>
        ty.infer // FIXME NOW this seems wrong, what if we annotate the level? generally we want to make sure this is working as intent
      case Unglue(ty, _, _) => ty
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

object BuiltIn {
  var equiv: Value = null
  var fiber_at: Value = null
  var fiber_at_ty: Value = null
  var equiv_of: Value = null
  var path_to_equiv: Value = null
}
