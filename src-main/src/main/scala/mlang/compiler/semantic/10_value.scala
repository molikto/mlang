package mlang.compiler.semantic

import mlang.compiler.GenLong.Negative.{dgen, gen}
import mlang.utils._
import mlang.compiler.{Pattern, EType}
import mlang.compiler.semantic.Formula
import scala.annotation.Annotation
import scala.collection.mutable
import ValueFibrant._

case class ImplementationLimitationCannotTransformOpenMeta() extends Exception


import Value._

sealed trait MetaState
object MetaState {
  case class Closed(v: Value) extends MetaState
  case class Open(id: Long, @type_annotation typ: Value) extends MetaState
}

case class Case(pattern: Pattern, closure: MultiClosure) {
  private def extract(pattern: Pattern, v: Value): Option[(Seq[Value], Seq[Formula])] = {
    val vs = mutable.ArrayBuffer[Value]()
    val ds = mutable.ArrayBuffer[Formula]()
    def rec(pattern: Pattern, v: Value): Boolean = {
      pattern match {
        case Pattern.GenericValue =>
          vs.append(v)
          true
        case Pattern.GenericDimension => logicError()
        case Pattern.Make(names) =>
          v.whnf match {
            case Make(values) =>
              names.zip(values).forall(pair => rec(pair._1, pair._2))
            case _ =>
              false
          }
        case Pattern.Construct(name, pt) =>
          v.whnf match {
            case Construct(n, values, dms, _) if name == n =>
              if (values.size + dms.size != pt.size) logicError()
              val dps = pt.drop(values.size)
              assert(dps.forall(_ == Pattern.GenericDimension))
              val ret = pt.take(values.size).zip(values).forall(pair => rec(pair._1, pair._2))
              ds.appendAll(dms)
              ret
            case _ =>
              false
          }
      }
    }
    if (rec(pattern, v)) {
      Some((vs.toSeq, ds.toSeq))
    } else {
      None
    }
  }
  def tryApp(v: Value): Option[Value] = extract(pattern, v).map(a => closure(a._1, a._2))
}

sealed trait Recursively
case class Inductively(@nominal_equality id: Long, @type_annotation typ: Value, ps: Seq[Value]) extends Recursively {
  def typFinal: Value = ps.foldLeft(typ) { (t, p) => t.whnf.asInstanceOf[Function].codomain(p) }
}


sealed trait Value {
  // we use referential equality for Value class, these is not the conversion checking, and only used by caching
  final override def equals(obj: Any): Boolean = (this, obj) match {
    case (r: Value, j: Value) => r.eq(j)
    case _ => logicError()
  }
  final override def hashCode(): Int = java.lang.System.identityHashCode(this)

  private[Value] var _from: Value = _
  private[Value] var _whnfCache: Value = _

  protected def getWhnf(): Value

  def whnf: Value = {
    val cached = _whnfCache
    if (cached == null) {
      val candidate =  getWhnf()
      if (NORMAL_FORM_MODEL) {
        _whnfCache = candidate
      }
      if (candidate != this /* this is a end of whnf chain */ &&
        candidate._from != candidate /* candidate is not a reference */ &&
        (candidate._from == null || (candidate._from._from != candidate._from)) /* ! candidate has a from that is a reference */
      ) candidate._from = this
      candidate
    } else {
      cached
    }
  }

  def simplify: Value = this match {
    case Projection(Make(vs), i) => vs(i).simplify
    case _ => this
  }

  // this can be considered a inverse of whnf
  def bestReifyValue: Value = (this match {
    case r: Reference => 
      r.value match {
        case g: Reference => g.bestReifyValue
        case _ => r
      }
    case Projection(Make(vs), i) => vs(i).bestReifyValue
    case Meta(MetaState.Closed(v)) =>
      v match {
        case r: Referential => r.bestReifyValue
        case _ => this
      }
    case v =>
      if (v._from == null) v else v._from
  }).simplify


  private[Value] def inferEndpoint(b: Boolean): Value = inferHelper.whnf match {
    case PathType(_, left, right) =>
      (if (b) right else left)
    case _ => logicError()
  }

  // only used by inferEndpoint, in general we cannot infer types, this might be inconsistent with subtyping
  // but endpoints is subtyping invarient
  private def inferHelper: Value = {
    whnf match {
      case g: Generic =>
        g.typ
      case App(l1, a1) =>
        // l1 cannot be a actual lambda, the real blocker of whnf is only open reference/meta
        l1.inferHelper.whnf match {
          case Function(_, _, c) =>
            c(a1)
          case _ => logicError()
        }
      case Projection(m1, f1) =>
        m1.inferHelper.whnf match {
          case rr: Record  => rr.projectedType(m1, f1)
          case _ => logicError()
        }
      case PatternRedux(l1, s1) =>
        l1.typ(s1)
      case PathApp(l1, d1) =>
        l1.inferHelper.whnf match {
          case PathType(typ, _, _) => typ(d1)
          case _ => logicError()
        }
      case h: Hcomp => h.tp
      case t: Transp => t.tp(Formula.True)
      case h: Comp => h.tp(Formula.True)
      case Unglue(ty, _, _, _) => ty
      case _ => logicError()
    }
  }


  // FIXME current problems of restriction/fswap system:
  // they have overlapping, fswap by constant is similar to restriction, but they produce
  // referential different terms (this is not a bug, but is a dirtyness)
  // newly produced local referenctal has the problem that they will not be compared by reference
  // easily, (again, not a bug, only dirtyness)
  // but I think we can currently
  // without fswap, the first problem dispears
  def support(): Support = Nominal_support(this)
}

object Value {

  var NORMAL_FORM_MODEL = false

  // these serve the purpose of recovering syntax
  sealed trait StableCanonical extends Value {
    override protected def getWhnf(): Value = this
  }
  sealed trait UnstableOrRedux extends Value
  sealed trait Unstable extends UnstableOrRedux
  sealed trait Redux extends UnstableOrRedux

  sealed trait Internal extends Value
  case class Derestricted(a: Value, asgn: Assignments) extends Internal {
    def getWhnf() = logicError()
  }


  // meta, reference, and generic
  // global and local
  // global ones can be lifted, has a root for lookup
  // local ones, can be restricted, has a roof for lookup
  sealed trait Referential extends Value {
    _from = this
    type Self <: Referential
    def referenced: Value

    private[semantic] def getRestrict(asgs: Assignments): Self
    private[semantic] def getFswap(w: Long, z: Formula): Self

    def lookupChildren(v: Referential): Option[Assignments]
  }

  sealed trait LocalReferential extends Referential {
    type Self <: LocalReferential

    def lookupChildren(v: Referential): Option[Assignments] = {
      if (this == v) {
        Some(Set.empty)
      } else {
        assert(childRestricted == null) // you can only lookup children from root
        if (restrictedCache != null) restrictedCache.find(_._2 == v).map(_._1)
        else None
      }
    }

    private var supportCache: Support = null

    private[semantic] def supportCached() : Support = {
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

    // LATER merge the two into one variable?? it is confusing though
    // only not null for parents
    private var restrictedCache: mutable.Map[Assignments, LocalReferential] = null
    // only not null for children
    private var childRestricted: (LocalReferential, Assignments) = null
    private var fswapCache: mutable.Map[(Long, Formula), LocalReferential] = null
    protected def clearSavedAfterValueChange(): Unit = {
      if (childRestricted != null) logicError() // you don't want to do this
      supportCache = null
      restrictedCache = null
    }

    protected def createNewEmpty(): Self
    protected def restrictAndInitContent(s: Self, assignments: Assignments): Unit
    protected def fswapAndInitContent(s: Self, w: Long, z: Formula): Unit

    private[semantic] def getFswap(w: Long, z: Formula): Self = {
      val spt = support()
      if (spt.openMetas.nonEmpty) {
        throw ImplementationLimitationCannotTransformOpenMeta()
      }
      if (!spt.names.contains(w)) {
        this.asInstanceOf[Self]
      } else {
        if (fswapCache == null) fswapCache = mutable.Map()
        val key = (w, z)
        fswapCache.get(key) match {
          case Some(r) => r.asInstanceOf[Self]
          case None =>
            val n = createNewEmpty()
            fswapCache.put(key, n)
            fswapAndInitContent(n, w, z)
            n
        }
      }
    }

    private[semantic] def getRestrict(assigments: Assignments): Self = {
      if (childRestricted != null) { // direct to parent
        childRestricted._1.asInstanceOf[Referential].getRestrict(childRestricted._2 ++ assigments).asInstanceOf[Self]
      } else {
        val spt = support() // this will re-calculate the support if metas changed
        if (spt.openMetas.nonEmpty) {
          throw ImplementationLimitationCannotTransformOpenMeta()
        }
        val asgg = assigments.filter(a => spt.names.contains(a._1))
        if (asgg.isEmpty) {
          this.asInstanceOf[Self]
        } else {
          if (restrictedCache == null) restrictedCache = mutable.Map()
          // debug(s"getting restricted value by $asgg", 2)
          restrictedCache.get(asgg) match {
            case Some(r) => r.asInstanceOf[Self]
            case None =>
              val n = createNewEmpty()
              n.childRestricted = (this, asgg)
              n.supportCache = Support(spt.generic, spt.names -- asgg.map(_._1), spt.openMetas)
              restrictedCache.put(asgg, n)
              restrictAndInitContent(n, asgg)
              n
          }
        }
      }
    }
  }



  object Meta {
    def uninitalized(): Meta = Meta(null)
    def solved(a: Value) = Meta(MetaState.Closed(a))
  }
  case class Meta(private[Value] var _state: MetaState) extends LocalReferential {
    override type Self = Meta

    def solved: Value = state.asInstanceOf[MetaState.Closed].v
    def isSolved: Boolean = state.isInstanceOf[MetaState.Closed]

    def state_=(a: MetaState) = {
      clearSavedAfterValueChange()
      _state = a
      if (debug.enabled) assert(isSolved)
    }
    def state = _state

    override def referenced: Value = state match {
      case MetaState.Closed(v) => v
      case MetaState.Open(id, typ) => typ
    }

    override protected def getWhnf(): Value = _state match {
      case o: MetaState.Open => this
      case MetaState.Closed(v) => v.whnf
    }

    def initialize(a: Value): Unit = {
      assert(_state == null)
      _state = MetaState.Closed(a)
    }

    override protected def createNewEmpty(): Meta = Meta(null)
    override protected def restrictAndInitContent(s: Meta, assignments: Assignments): Unit = state match {
      case MetaState.Closed(v) => s._state = MetaState.Closed(v.restrict(assignments))
      case _: MetaState.Open => throw ImplementationLimitationCannotTransformOpenMeta()
    }
    override protected def fswapAndInitContent(s: Meta, w: Long, z: Formula): Unit = state match {
      case MetaState.Closed(v) => s._state = MetaState.Closed(v.fswap(w, z))
      case _: MetaState.Open => throw ImplementationLimitationCannotTransformOpenMeta()
    }
  }

  
  sealed trait Reference extends Referential {
    override def toString: String = "Reference"
    var value: Value
    def referenced = value
    override protected def getWhnf(): Value = referenced.whnf
  }

  object GlobalReference {
    def apply(to: Value, name: Name = null): GlobalReference = {
      val g = GlobalReference(to)
      g.name = name
      g
    }
  }
  case class GlobalReference(@lateinit var value: Value) extends Reference {
    var name: Name = null
    override type Self = GlobalReference

    override private[semantic] def getRestrict(asgs: Assignments): Self = this.asInstanceOf[Self]
    private[semantic] def getFswap(w: Long, z: Formula): Self = this.asInstanceOf[Self]
    override def support(): Support = Support.empty
    def lookupChildren(a: Referential): Option[Assignments] = a match {
      case b: Reference => if (b.value == value) Some(Set.empty) else None
      case _ => None
    }
  }

  object LocalReference {
    def uninitalized(): LocalReference = LocalReference(null)
  }
  case class LocalReference(@lateinit private var _value: Value) extends Reference with LocalReferential {
    def initialize(v: Value): Unit = {
      assert(_value == null)
      _value = v
    }

    override def value_=(a: Value): Unit = {
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
    private[semantic] val HACK = Generic(0, null)
    private[semantic] val HACKS = (0 until 20).map(_ => HACK)
  }

  case class Generic(val id: Long, @type_annotation @lateinit protected var _typ: Value) extends LocalReferential {
    override type Self = Generic

    def typ_=(a: Value) = {
      clearSavedAfterValueChange()
      _typ = a
    }
    def typ = _typ

    def initialize(a: Value) = {
      assert(_typ == null)
      _typ = a
    }

    override def referenced: Value = _typ
    override protected def getWhnf() = this
    override protected def createNewEmpty(): Generic = Generic(id, null)
    override protected def restrictAndInitContent(s: Generic, assignments: Assignments) =
      s._typ = typ.restrict(assignments)

    override protected def fswapAndInitContent(s: Generic, w: Long, z: Formula) =
      logicError() // currently we only use fresh variable, and fresh variable should not generate new generic supported
  }


  //
  //
  //
  // 
  //
  //
  //

  case class Universe(level: Int) extends StableCanonical

  object Universe {
    val TYPE_IN_TYPE = false
    def suc(i: Int) = Universe(if (TYPE_IN_TYPE) 0 else i + 1)
    def level0 = Universe(0)
    def level1 = Universe(if (TYPE_IN_TYPE) 0 else 1)
  }

  case class Function(etype: EType.Function, domain: Value, codomain: Closure) extends StableCanonical

  /**
    * whnf: lambda is whnf and is not a canonical
    */
  case class App(@stuck_pos lambda: Value, argument: Value) extends Redux {
    override protected def getWhnf(): Value = {
      val lam = lambda.whnf
      inline def default() = 
          if (lam == lambda) this else App(lam, argument)
      lam match {
        case Lambda(closure) =>
          closure(argument).whnf
        case p : PatternLambda =>
          PatternRedux(p, argument).whnf
        case Hcomp(tp, base, faces) =>
          tp.whnf match {
            case Function(d, i, c) =>
              Hcomp(c(argument), App(base, argument), faces.view.mapValues(v => v.map(a => App(a, argument))).toMap)
            case _ => default()
          }
        case Transp(tp, phi, base) =>
          val dim = dgen()
          tp.apply(Formula.Generic(dim)).whnf match {
            case _: Function =>
              inline def tpr(i: Formula) = tp(i).whnf.asInstanceOf[Function]
              Transp(
                i => tpr(i).codomain(transpFill_inv(i, phi, j => tpr(j).domain, argument)),
                phi,
                App(base, transp_inv(phi, i => tpr(i).domain, argument))
              )
            case _ => default()
          }

        case lam => default()
      }
    }
  }

  def apps(maker: Value, values: Seq[Value]) : Value = values.foldLeft(maker) { (m: Value, v: Value) => Value.App(m, v) }

  case class Lambda(closure: Closure) extends StableCanonical


  // the reason we must have a domain here is because we support unordered pattern matching
  // so pattern redux can be stuck value when non of their arguments is stuck
  // LATER(PATTERN) is unordered pattern matching really a good thing? but I don't want case trees!
  case class PatternLambda(@nominal_equality id: Long, @type_annotation domain: Value, @type_annotation typ: Closure, cases: Seq[Case]) extends StableCanonical

  /**
    * whnf: stuck is whnf AND pattern redux cannot continue
    */
  case class PatternRedux(lambda: PatternLambda, @stuck_pos stuck: Value) extends Redux {
    override protected def getWhnf(): Value = {
      // using first match is even ok for overlapping ones
      var res: Value = null
      lambda.domain.whnf match {
        case s: Sum if s.hit =>
          stuck.whnf match {
            case Hcomp(ty, base, faces) =>
              // non-dependent codomain
              val d = Generic(gen(), null)
              val ret = lambda.typ(d)
              // RULES cubicaltt doesn't have this actually, it seems not that necessary
              if (ret.support().generic.contains(d)) {
                res = Comp(
                  AbsClosure(i => lambda.typ(hfill(ty, base, faces)(i))),
                  PatternRedux(lambda, base), faces.view.mapValues(_.map(v => PatternRedux(lambda, v))).toMap)
              } else {
                res = Hcomp(ret, PatternRedux(lambda, base), faces.view.mapValues(_.map(v => PatternRedux(lambda, v))).toMap)
              }
            case _ =>
          }
        case _ =>
      }
      var cs = lambda.cases
      while (cs.nonEmpty && res == null) {
        res = cs.head.tryApp(stuck).orNull
        cs = cs.tail
      }
      if (res == null) {
        val ss = stuck.whnf
        if (ss == stuck) this else PatternRedux(lambda, ss)
      } else {
        res.whnf
      }
    }
  }


  case class Record(
    etype: EType.Record,
    inductively: Option[Inductively],
    nodes: ClosureGraph) extends StableCanonical {
    assert(etype.names.size == nodes.size)
    def projectedType(values: Value, name: Int): Value =
      nodes.get(name, i => Projection(values, i))
  }

  case class Make(values: Seq[Value]) extends StableCanonical

  /**
    * whnf: make is whnf and is not canonical
    */
  case class Projection(@stuck_pos make: Value, field: Int) extends Redux {
    override protected def getWhnf(): Value = {
      make.whnf match {
        case Make(vs) => vs(field).whnf
        case a: StableCanonical =>
          logicError()
        case p => if (p == make) this else Projection(p, field)
      }
    }
  }

  case class SimpleConstruct(name: Int, vs: Seq[Value]) extends StableCanonical
  case class HitConstruct(name: Int, vs: Seq[Value], @stuck_pos ds: Seq[Formula], @type_annotation ty: ValueSystem) extends Unstable {
    override protected def getWhnf() = 
      ty.find(_._1.nfTrue) match {
        case Some(value) => value._2().whnf
        case None => this
      }
  }
  object Construct {
    def unapply(v: Value): Option[(Int, Seq[Value], Seq[Formula], ValueSystem)] = v match {
      case SimpleConstruct(n, vs) => Some((n, vs, Seq.empty, Map.empty))
      case HitConstruct(n, vs, ds, ty) => Some((n, vs, ds, ty))
      case _ => None
    }
    def apply(n: Int, vs: Seq[Value]): SimpleConstruct = SimpleConstruct(n, vs)
    def apply(n: Int, vs: Seq[Value], ds: Seq[Formula], ty: ValueSystem) = 
      if (ds.isEmpty) { assert(ty.isEmpty); SimpleConstruct(n, vs) }
      else HitConstruct(n, vs, ds, ty)
  }


  case class Sum(etype: EType.Sum, inductively: Option[Inductively], hit: Boolean, constructors: Seq[ClosureGraph]) extends StableCanonical {
    def noArgs = inductively.forall(_.ps.isEmpty)
  }

  case class PathType(typ: AbsClosure, left: Value, right: Value) extends StableCanonical
  case class PathLambda(body: AbsClosure) extends StableCanonical

  /**
    * whnf: left is whnf but not canonical, and dimension is not constant
    */
  case class PathApp(@stuck_pos left: Value, @stuck_pos dimension: Formula) extends UnstableOrRedux {
    override protected def getWhnf(): Value = left.whnf match {
      case PathLambda(c) =>
        c(dimension).whnf
      case canonical: StableCanonical => logicError()
      case a =>
        dimension.normalForm match {
          case NormalForm.True =>
            a.inferEndpoint(true).whnf
          case NormalForm.False =>
            a.inferEndpoint(false).whnf
          case _ =>
            if (a == left) this else PathApp(a, dimension.simplify)
        }
    }
  }


  /**
    * whnf: tp on a generic value cannot reduce to a canonical, or base is not canonical in case sum type
    */
  case class Transp(
      @stuck_pos tp: AbsClosure,
      phi: Formula,
      @stuck_pos base: Value // it stuck here on sum type sometimes
  ) extends UnstableOrRedux {
    override protected def getWhnf(): Value = {
      val t = transpBody(this)
      if (t == this) this else t.whnf
    }
  }

  // TODO when we have a syntax for partial values, these should be removed? or this should stay as primitive because we need it?
  case class Comp(@stuck_pos tp: AbsClosure, base: Value, faces: AbsClosureSystem) extends Redux {
    override protected def getWhnf(): Value = comp(tp, base, faces).whnf
  }


  /**
    * whnf: tp is whnf and not canonical, or tp is sum or u, base is whnf
    */
  case class Hcomp(@type_annotation @stuck_pos tp: Value, base: Value, faces: AbsClosureSystem) extends Redux {
    override protected def getWhnf(): Value = {
      val t = hcompBody(this)
      if (t == this) this else t.whnf
    }
  }

  /**
    * whnf: faces is not constant
    */
  case class GlueType(@type_annotation ty: Value, @stuck_pos faces: ValueSystem) extends Unstable {
    override protected def getWhnf(): Value = faces.find(_._1.nfTrue).map(b => Projection(b._2(), 0).whnf).getOrElse(this)
  }
  /**
    * whnf: faces is not constant
    */
  case class Glue(m: Value, @stuck_pos faces: ValueSystem) extends Unstable {
    override protected def getWhnf() =
      faces.find(_._1.nfTrue).map(_._2().whnf).getOrElse(this)
  }
  /**
    * whnf: faces is not constant, base is whnf, and base's whnf is not glue
    * LATER this is how the whnf is defined, so glue is considered canonical, but unglue is not
    */
  case class Unglue(ty: Value, base: Value, isU: Boolean, @stuck_pos faces: ValueSystem) extends Redux {
    override protected def getWhnf(): Value = {
      val red = faces.find(_._1.nfTrue).map(b => {
        if (isU) transp_inv(Formula.False, b._2().whnf.asInstanceOf[PathLambda].body, base).whnf
        else App(Projection(Projection(b._2(), 1), 0), base).whnf
      })
      red match {
        case Some(a) => a
        case None =>
          val bf = base.whnf
          bf match {
            case Glue(b, _) =>
               b.whnf
            case _ =>
              if (bf == base) this else Unglue(ty, bf, isU, faces)
          }
      }
    }
  }
}