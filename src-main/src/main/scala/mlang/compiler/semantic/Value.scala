package mlang.compiler.semantic

import mlang.compiler.GenLong.Negative.{dgen, gen}
import mlang.utils._
import mlang.compiler.Pattern
import mlang.compiler.semantic.Formula

import scala.annotation.Annotation
import scala.collection.mutable

case class ImplementationLimitationCannotRestrictOpenMeta() extends Exception

def (f: Formula) supportShallow(): SupportShallow = SupportShallow(f.names, Set.empty)

// FIXME: move out whnf
object Value {


  // these serve the purpose of recovering syntax
  sealed trait StableCanonical extends Value
  // FIXME hcomp is either unstable canonical or redux, depending on the type
  sealed trait UnstableCanonical extends Value // this value can reduce more, but only when restricted
  sealed trait Redux extends Value {
    // FIXME this is not that well defined, since some term will always whnf on arguments, some not
    // maybe inline in whnf
    def reduce(): Option[Value]


    override def reduceOrSelf() = reduce().getOrElse(this)

    @inline def reduceThenWhnfOrSelf() = reduce() match {
      case Some(r) => r.whnf
      case _ => this
    }
  }


  sealed trait Referential extends Value {
    _from = this
    type Self <: Referential
    private[Value] def getRestrict(asgs: Assignments): Self
    private[Value] def getFswap(w: Long, z: Formula): Self
    def lookupChildren(v: Referential): Option[Assignments]
    def referenced: Value

}

  sealed trait Reference extends Referential {
    override def toString: String = "Reference"
    var value: Value
    def referenced = value

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

    private[Value] def getFswap(w: Long, z: Formula): Self = {
      if (z == Formula.True || z == Formula.False) {
        // these get cached...
        getRestrict(Set((w, z == Formula.True)))
      } else {
        //      if (this.isInstanceOf[Value.Generic]) {
        //        this.asInstanceOf[Self]
        //      } else {
        val spt = support()
        if (spt.openMetas.nonEmpty) {
          throw ImplementationLimitationCannotRestrictOpenMeta()
        }
        if (!spt.names.contains(w)) {
          this.asInstanceOf[Self]
        } else {
          if (fswapCache == null) fswapCache = mutable.Map()
          // debug(s"getting fswap value by $w, $z", 2)
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
    }

    private[Value] def getRestrict(assigments: Assignments): Self = {
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

    def lookupChildren(v: Referential): Option[Assignments] = {
      if (this == v) {
        Some(Set.empty)
      } else {
        assert(childRestricted == null) // you can only lookup children from root
        if (restrictedCache != null) restrictedCache.find(_._2 == v).map(_._1)
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

    override def reduceOrSelf(): Value = if (isSolved) solved else this
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
      case _: MetaState.Open => throw ImplementationLimitationCannotRestrictOpenMeta()
    }
    override protected def fswapAndInitContent(s: Meta, w: Long, z: Formula): Unit = state match {
      case MetaState.Closed(v) => s._state = MetaState.Closed(v.fswap(w, z))
      case _: MetaState.Open => throw ImplementationLimitationCannotRestrictOpenMeta()
    }

    override def referenced: Value = state match {
      case MetaState.Closed(v) => v
      case MetaState.Open(id, typ) => typ
    }
}


  case class GlobalReference(@lateinit var value: Value) extends Reference {
    var name: Name = null
    override type Self = GlobalReference
    override private[Value] def getRestrict(asgs: Assignments): GlobalReference = this
    private[Value] def getFswap(w: Long, z: Formula): Self = this
    def lookupChildren(v: Referential): Option[Assignments] = if (this == v) Some(Set.empty) else None
    override def supportShallow(): SupportShallow = SupportShallow.empty
    override def support(): Support = Support.empty

    override def reduceOrSelf(): Value = referenced
}

  case class LocalReference(@lateinit private var _value: Value) extends LocalReferential with Reference {

    override def reduceOrSelf(): Value = referenced

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
    private[semantic] val HK = Generic(0, null)
    private[semantic] val HKS = (0 until 40).map(_ => HK)
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


  case class Universe(level: Int) extends StableCanonical

  object Universe {
    val TypeInType = true
    def suc(i: Int) = Universe(if (TypeInType) 0 else i)
    def level0 = Universe(0)
    def level1 = Universe(if (TypeInType) 0 else 1)
  }

  case class Function(domain: Value, impict: Boolean, codomain: Closure) extends StableCanonical

  /**
    * whnf: lambda is whnf and is not a canonical
    */
  case class App(@stuck_pos lambda: Value, argument: Value) extends Redux {
    def reduce(): Option[Value] = {
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
  case class Lambda(closure: Closure) extends StableCanonical
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

  // the reason we must have a domain here is because we support unordered pattern matching
  // so pattern redux can be stuck value when non of their arguments is stuck
  // LATER(PATTERN) is unordered pattern matching really a good thing? but I don't want case trees!
  case class PatternLambda(@nominal_equality id: Long, @type_annotation domain: Value, @type_annotation typ: Closure, cases: Seq[Case]) extends StableCanonical

  /**
    * whnf: stuck is whnf AND pattern redux cannot continue
    */
  case class PatternRedux(lambda: PatternLambda, @stuck_pos stuck: Value) extends Redux {
    def reduce(): Option[Value] = {
      // using first match is even ok for overlapping ones
      var res: Value = null
      lambda.domain.whnf match {
        case s: Sum if s.hit =>
          stuck.whnf match {
            case Hcomp(ty, base, faces) =>
              // non-dependent codomain
              val ge = gen()
              val d = Value.Generic(ge, null)
              val ret = lambda.typ(d)
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
      Option(res)
    }
  }


  sealed trait RecursiveType
  case class Inductively(@nominal_equality id: Long, @type_annotation typ: Value, ps: Seq[Value]) extends RecursiveType {
    def restrict(lv: Assignments): Inductively = Inductively(id, typ.restrict(lv), ps.map(_.restrict(lv)))
    def fswap(w: Long, z: Formula): Inductively = Inductively(id, typ.fswap(w, z), ps.map(_.fswap(w, z)))
    def supportShallow(): SupportShallow =  typ.supportShallow() ++ ps.map(_.supportShallow()).merge

    def typFinal: Value = ps.foldLeft(typ) { (t, p) => t.whnf.asInstanceOf[Function].codomain(p) }
  }

  case class Record(
      inductively: Option[Inductively],
      names: Seq[Name],
      nodes: ClosureGraph) extends StableCanonical {
    assert(names.size == nodes.size)
    def projectedType(values: Value, name: Int): Value = {
      nodes.get(name, i => Projection(values, i))
    }
  }
  case class Make(values: Seq[Value]) extends StableCanonical

  /**
    * whnf: make is whnf and is not canonical
    */
  case class Projection(@stuck_pos make: Value, field: Int) extends Redux {
    def reduce(): Option[Value] = {
      make match {
        case Make(vs) => Some(vs(field))
        case a: StableCanonical =>
          logicError()
        case _ => None
      }
    }
  }

  // ty == null when ds.isEmpty
  case class Construct(name: Int, vs: Seq[Value], ds: Seq[Formula], @type_annotation ty: ValueSystem) extends UnstableCanonical
  case class Constructor(name: Name, nodes: ClosureGraph) {
    def restrict(lv: Assignments): Constructor = Constructor(name, nodes.restrict(lv))
    def fswap(w: Long, z: Formula): Constructor = Constructor(name, nodes.fswap(w, z))
  }

  case class Sum(inductively: Option[Inductively], hit: Boolean, constructors: Seq[Constructor]) extends StableCanonical {
    def noArgs = inductively.forall(_.ps.isEmpty)
  }

  case class PathType(typ: AbsClosure, left: Value, right: Value) extends StableCanonical
  case class PathLambda(body: AbsClosure) extends StableCanonical

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
            left match {
              case canonical: StableCanonical => logicError()
              case _ => None
            }
        }
    }
  }


  // create a path from base  => transp, tp is constant on phi
  def transpFill(i: Formula, phi: Formula, tp: AbsClosure, base: Value) =
    Transp(AbsClosure(j => tp(Formula.And(i, j))), Formula.Or(Formula.Neg(i), phi), base)

  // from base => hcomp
  def hfill(tp: Value, base: Value, faces: AbsClosureSystem) = {
    AbsClosure(i =>
      Hcomp(tp, base,
        faces.view.mapValues(f => AbsClosure(j => f(Formula.And(i, j)))).toMap.updated(Formula.Neg(i), AbsClosure(_ => base)))
    )
  }

  def gfill(tp: AbsClosure, base: Value, faces: AbsClosureSystem) = {
    AbsClosure(i =>
      gcomp(AbsClosure(j => tp(Formula.And(i, j))),
        base,
        faces.view.mapValues(f => AbsClosure(j => f(Formula.And(i, j)))).toMap.updated(Formula.Neg(i), AbsClosure(_ => base)))
    )
  }

  // from base => com
  def fill(tp: AbsClosure, base: Value, faces: AbsClosureSystem) = {
    AbsClosure(i =>
      Comp(AbsClosure(j => tp(Formula.And(i, j))),
        base,
        faces.view.mapValues(f => AbsClosure(j => f(Formula.And(i, j)))).toMap.updated(Formula.Neg(i), AbsClosure(_ => base)))
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

  // transp(A, p, a(0)) -> a(1)   : A(1)
  def squeeze(A: AbsClosure, a: AbsClosure, p: Formula) =
    AbsClosure(i => Transp(AbsClosure(j => A(Formula.Or(i, j))), Formula.Or(p, i), a(i)))


  def transpFill(graph0: ClosureGraph, graph: Formula => ClosureGraph, phi: Formula, base: Int => Value): Seq[AbsClosure] = {
    val closures = mutable.ArrayBuffer[AbsClosure]()
    for (i <- graph0.graph.indices) {
      val res = graph0(i) match {
        case _: ClosureGraph.Independent =>
          AbsClosure(j => {
            transpFill(j,
              phi,
              AbsClosure(k => graph(k).graph(i).independent.typ),
              base(i)
            )
          })
        case _: ClosureGraph.Dependent =>
          AbsClosure(j => {
            transpFill(j,
              phi,
              AbsClosure(k => {val tt = graph(k); tt.get(i, j => closures(j)(k))  }),
              base(i)
            )
          })
      }
      closures.append(res)
    }
    closures.toSeq
  }

  /**
    * whnf: tp on a generic value cannot reduce to a canonical, or base is not canonical in case sum type
    */
  case class Transp(
      @stuck_pos tp: AbsClosure,
      phi: Formula,
      @stuck_pos base: Value // it stuck here on sum type sometimes
  ) extends Redux {

    override def reduce(): Option[Value] = {
      if (phi.normalFormTrue) {
        Some(base)
      } else {
        val dim = Formula.Generic(dgen())
        val res: Value = tp.apply(dim).whnf match {
          case _: Function =>
            def tpr(i: Formula) = tp(i).whnf.asInstanceOf[Function]
            Lambda(Closure(v => {
              def w(i: Formula) = transpFill_inv(i, phi, AbsClosure(a => tpr(a).domain), v)
              val w0 = transp_inv(phi, AbsClosure(a => tpr(a).domain), v)
              Transp(AbsClosure(i => tpr(i).codomain(w(i))), phi, App(base, w0))
            }))
          case _: PathType =>
            def tpr(i: Formula) = tp(i).whnf.asInstanceOf[PathType]
            PathLambda(AbsClosure(dim => {
              Comp(
                AbsClosure(i => tpr(i).typ(dim)),
                PathApp(base, dim),
                Seq(
                  (phi, AbsClosure(_ => PathApp(base, dim))),
                  (Formula.Neg(dim), AbsClosure(a => tpr(a).left)),
                  (dim, AbsClosure(a => tpr(a).right))
                ).toMap)
            }))
          case r: Record =>
            if (r.nodes.isEmpty) {
              base
            } else {
              def tpr(i: Formula) = tp(i).whnf.asInstanceOf[Record].nodes
              val closures = transpFill(r.nodes, tpr, phi, i => Projection(base, i))
              Make(closures.map(_.apply(Formula.True)))
            }
          case s: Sum =>
            if (s.noArgs) {
              base
            } else {
              base.whnf match {
                case Construct(c, vs, rs, d) =>
                  def tpr(i: Formula) = tp(i).whnf.asInstanceOf[Sum].constructors(c)
                  val cc = s.constructors(c)
                  val theta = transpFill(cc.nodes, i => tpr(i).nodes, phi, vs)
                  val w1p = Construct(c, theta.map(_.apply(Formula.True)), rs, d)
                  if (rs.isEmpty) {
                    w1p
                  } else {
                    val item1 = (phi, AbsClosure(_ => base))
                    def alpha(e: AbsClosure) = squeeze(tp, e, phi)
                    val items = cc.nodes.reduce(rs).phi().toSeq.map(f => {
                      val e = AbsClosure(i => tpr(i).nodes.reduceAll(theta.map(_.apply(i))).reduce(rs).restrictions().find(_._1 == f).get._2)
                      val abs = AbsClosure(i => alpha(e)(Formula.Neg(i)))
                      (f, abs)
                    }).toMap.updated(item1._1, item1._2)
                    Hcomp(tp(Formula.True), w1p, items)
                  }
                case Hcomp(hty, hbase, faces) =>
                  Hcomp(tp(Formula.True), Transp(tp, phi, hbase), faces.map(pr => (pr._1, pr._2.map(v => Transp(tp, phi, v)))))
                case _: StableCanonical => logicError()
                case _ =>
                  null
              }
            }
          case g: GlueType =>
            transpGlue(g, dim, phi, base)
          case Hcomp(Universe(_), b0, faces) =>
            transpHcompUniverse(b0, faces, dim, phi, base)
          case _: Universe =>
            base
          case _ => null
        }
        Option(res)
      }
    }
  }

  def transpHcompUniverse(A: Value, es: AbsClosureSystem, dim: Formula.Generic, si: Formula, u0: Value): Value = {
    // this mapping is done in hcomp in cubicaltt
    val A0 = A.fswap(dim.id, Formula.False)
    val A1 = A.fswap(dim.id, Formula.True)
    val es0 = es.fswap(dim.id, Formula.False)
    val es1 = es.fswap(dim.id, Formula.True)

    // this is UnglueU in cubicaltt, the es0 is a system of path lambdas
    val v0 = Unglue(A0, u0, true, es0.view.mapValues(a => PathLambda(a)).toMap)

    val faces_elim_dim = es.toSeq.map(a => (a._1.elim(dim.id), a._2)).filter(_._1.normalForm != NormalForm.False).toMap
    val t1s = faces_elim_dim.view.mapValues(p => {
      Transp(AbsClosure(i => p(Formula.True).fswap(dim.id, i)), si, u0)
    }).toMap
    val v1 = comp(AbsClosure(i => A.fswap(dim.id, i)), v0,
      faces_elim_dim.map((pair: (Formula, AbsClosure)) => {
        val abs = AbsClosure(i => {
          transp_inv(Formula.False, pair._2.fswap(dim.id, i),
            transpFill(i, si, AbsClosure(i => pair._2(Formula.True).fswap(dim.id, i)), u0)
          )
        })
        (pair._1, abs)
      }).updated(si, AbsClosure(_ => v0)))
    val sys = t1s.updated(si, u0)
    val fibersys_ = es1.map((pair: (Formula, AbsClosure)) => {
      val eq = pair._2
      val b = v1
      val as = sys
      val dg = Formula.Generic(dgen())
      val res = eq(dg).whnf match {
        case s: Sum if s.noArgs =>
          // because we know this is non-dependent
          val p1 = Hcomp(eq(dg), b, as.view.mapValues(a => AbsClosure(_ => a)).toMap)
          val p2 = hfill(eq(dg), b, as.view.mapValues(a => AbsClosure(_ => a)).toMap)
          (p1: Value, p2: AbsClosure)
        case other =>
          val adwns = as.map((pair: (Formula, Value)) => {
            (pair._1, AbsClosure(j => transpFill_inv(j, Formula.False, eq, pair._2)))
          }).toMap
          val left = fill(eq, b, adwns)
          val a = comp(eq, b, adwns)
          val right = AbsClosure(j =>
            transpFill_inv(j, Formula.False, eq, a)
          )
          val p = AbsClosure(i =>
            comp(AbsClosure(a => eq(Formula.Neg(a))), a,
              adwns.updated(Formula.Neg(i), left).updated(i, right).view.mapValues(v => AbsClosure(j => v(Formula.Neg(j)))).toMap
            )
          )
          (a : Value, p: AbsClosure)
      }
      (pair._1, res)
    }).toMap
    val t1s_ = fibersys_.view.mapValues(_._1).toMap
    val v1_ = Hcomp(A1, v1, fibersys_.view.mapValues(_._2).toMap.updated(si, AbsClosure(_ => v1)))
    Glue(v1_, t1s_)
  }

  def transpGlue(B: GlueType, dim: Formula.Generic, si: Formula, u0: Value): Value = {
    def B_swap(f: Formula) = B.fswap(dim.id, f).asInstanceOf[GlueType]
    val B0 = B_swap(Formula.False)
    def A_swap(i: Formula) = B.ty.fswap(dim.id, i)
    val B1 = B_swap(Formula.True)
    val A1 = B1.ty
    val A0 = B0.ty
    // a0: A(i/0)
    val a0 = Unglue(A0, u0, false, B0.faces)
    // defined in phi_elim_i
    def t_tide(trueFace: Value, i: Formula) = {
      transpFill(i, si, AbsClosure(i => {
      Projection(trueFace.fswap(dim.id, i), 0)
      }), u0)
    }
    val faces_elim_dim = B.faces.toSeq.map(a => (a._1.elim(dim.id), a._2)).filter(_._1.normalForm != NormalForm.False).toMap
    val B1_faces = B1.faces.filter(_._1.normalForm != NormalForm.False)
    def t1(trueFace: Value) = t_tide(trueFace, Formula.True)
    // a1: A(i/1) and is defined on both si and elim(i, phi)
    val a1 = gcomp(
      AbsClosure(i => A_swap(i)),
      a0,
      faces_elim_dim.view.mapValues(tf => {
        AbsClosure(i => {
          val EQi  = tf.fswap(dim.id, i)
          val w = Projection(EQi, 1)
          App(Projection(w, 0), t_tide(tf, i))
        })
      }).toMap.updated(si, AbsClosure(_ => a0))
    )
    // ..., phi(i/1) |- (t1`, alpha) // true face must have (i/1)
    def pair(trueFace: Value) = {
      val w = Projection(trueFace, 1)
      val compo = App(Projection(w, 1), a1) // is_contr(fiber_at(w(i/1).1, a1))
      ghcomp(Apps(BuiltIn.fiber_at, Seq(Projection(trueFace, 0), A1, Projection(w, 0), a1)), Projection(compo, 0),
        faces_elim_dim.view.mapValues(tf => {
          AbsClosure(i => {
            val u = Make(Seq(t1(tf), PathLambda(AbsClosure(_ => a1))))
            PathApp(App(Projection(compo, 1), u), i)
          })
        }).toMap.updated(si, AbsClosure(i => {
          val u = Make(Seq(u0, PathLambda(AbsClosure(_ => a1))))
          PathApp(App(Projection(compo, 1), u), i)
        }))
      )
    }
    val a1p = Hcomp(A1, a1,
        B1_faces.view.mapValues(bd => {
          // alpha is of type f(t1p) == a1
          AbsClosure(j => PathApp(Projection(pair(bd), 1), Formula.Neg(j)) )
        }).toMap.updated(si, AbsClosure(_ => a1)))
      Glue(a1p, B1_faces.view.mapValues(bd => Projection(pair(bd), 0)).toMap)
  }

  def hcompGlue(B: GlueType, u0: Value, faces: AbsClosureSystem): Value = {
    def t_tide(trueFace: Value) = {
      hfill(Projection(trueFace, 0), u0, faces)
    }
    def t1(trueFace: Value) = t_tide(trueFace)(Formula.True)
    val a1 = Hcomp(B.ty, Unglue(B.ty, u0, false, B.faces),
      faces.view.mapValues(_.map(u => Unglue(B.ty, u, false, B.faces))).toMap ++
      B.faces.view.mapValues(pair => AbsClosure(i => {
        val w = Projection(pair, 1)
        val f = Projection(w, 0)
        App(f, t_tide(pair)(i))
      })).toMap
    )
    Glue(a1, B.faces.view.mapValues(bd => t1(bd)).toMap)
  }



  def ghcomp(@stuck_pos tp: Value, base: Value, faces: AbsClosureSystem) = {
    Hcomp(tp, base, faces.updated(Formula.Neg(Formula.Or(faces.keys)), AbsClosure(base)))
  }

  def comp(@stuck_pos tp: AbsClosure, base: Value, faces: AbsClosureSystem) = {
    def default() = {
      Hcomp(
        tp(Formula.True),
        Transp(tp, Formula.False, base),
        faces.view.mapValues(f => AbsClosure(i => forward(tp, i, f(i)))).toMap)
    }
    val dim = Formula.Generic(dgen())
    val appd = tp.apply(dim)
    appd.whnf match {
      case PathType(typ, left, right) =>
        PathLambda(AbsClosure(i => {
          Comp(tp.map(a => a.whnf.asInstanceOf[PathType].typ(i)), PathApp(base, i),
            faces.view.mapValues(_.map(a => PathApp(a, i))).toMap
              .updated(i, AbsClosure(j => tp(j).whnf.asInstanceOf[PathType].right))
              .updated(Formula.Neg(i).simplify, AbsClosure(j => tp(j).whnf.asInstanceOf[PathType].left))
          )
        }))
//      case r: Record =>
//        Make(compGraph(r.nodes, i => tp(i).whnf.asInstanceOf[Record].nodes, faces, base, (v, i) => Projection(v, i)))
      case s: Sum if !s.hit && s.noArgs =>
        assert(!appd.support().names.contains(dim.id))
        Hcomp(appd, base, faces)
      case _ =>
        default()
    }
  }
  def gcomp(@stuck_pos tp: AbsClosure, base: Value, faces: AbsClosureSystem) = {
    ghcomp(
      tp(Formula.True),
      Transp(tp, Formula.False, base),
      faces.view.mapValues(f => AbsClosure(i => forward(tp, i, f(i)))).toMap)
  }

  // FIXME when we have a syntax for partial values, these should be removed (or what? because Agda cannot compute the problem?)
  case class Comp(@stuck_pos tp: AbsClosure, base: Value, faces: AbsClosureSystem) extends Redux {
    override def reduce(): Option[Value] = Some(comp(tp, base, faces))
  }


  def compGraph(cs0: ClosureGraph, cs: Formula => ClosureGraph, faces: AbsClosureSystem, base: Value, map: (Value, Int) => Value): Seq[Value] = {
    val closures = mutable.ArrayBuffer[AbsClosure]()
    for (i <- cs0.graph.indices) {
      val res = cs0(i) match {
        case _: ClosureGraph.Independent =>
          fill(AbsClosure(j => cs(j)(i).asInstanceOf[ClosureGraph.Independent].typ), map(base, i),
            faces.view.mapValues(_.map(a => map(a, i))).toMap
          )
        case _: ClosureGraph.Dependent =>
          fill(
            AbsClosure(k => cs(k).get(i, j => closures(j)(k))),
            map(base, i),
            faces.view.mapValues(_.map(a => map(a, i))).toMap
          )
      }
      closures.append(res)
    }
    closures.toSeq.map(_.apply(Formula.True))
  }


  def hcompGraph(cs: ClosureGraph, faces: AbsClosureSystem, base: Value, map: (Value, Int) => Value): Seq[Value] = {
    val closures = mutable.ArrayBuffer[AbsClosure]()
    for (i <- cs.graph.indices) {
      val res = cs(i) match {
        case in: ClosureGraph.Independent =>
          hfill(in.typ, map(base, i),
            faces.view.mapValues(_.map(a => map(a, i))).toMap
          )
        case com: ClosureGraph.Dependent =>
          fill(
            AbsClosure(k => cs.get(i, j => closures(j)(k))),
            map(base, i),
            faces.view.mapValues(_.map(a => map(a, i))).toMap
          )
      }
      closures.append(res)
    }
    closures.toSeq.map(_.apply(Formula.True))
  }

  /**
    * whnf: tp is whnf and not canonical, or tp is sum or u, base is whnf
    */
  case class Hcomp(@type_annotation @stuck_pos tp: Value, base: Value, faces: AbsClosureSystem) extends Redux {

    override def reduce(): Option[Value] = {
      val res = faces.find(_._1.normalFormTrue) match {
        case Some(t) => t._2(Formula.True)
        case None =>
          val tp0 = tp.whnf
           tp0 match {
            case PathType(a, u, w) =>
               PathLambda(AbsClosure(j => Hcomp(
                 a(j),
                 PathApp(base, j),
                 faces.view.mapValues(_.map(v => PathApp(v, j))).toMap
                   .updated(Formula.Neg(j), AbsClosure(_ => u))
                   .updated(j, AbsClosure(_ => w))
               )))
            case Function(_, _, b) =>
               Lambda(Closure(v => Hcomp( b(v), App(base, v), faces.view.mapValues(_.map(j => App(j, v))).toMap)))
            case Record(_, _, cs) =>
              Make(hcompGraph(cs, faces, base, (v, i) => Projection(v, i)))
            case s@Sum(i, hit, cs) =>
              if (!hit) {
                base.whnf match {
                  case cc@Construct(c, vs, ds, ty) =>
                    if (s.noArgs) { // FIXME this doesn't seems to be correct!!! how to judge if the term is open or not
                      base
                    } else {
                      assert(ds.isEmpty)
                      Construct(c, hcompGraph(cs(c).nodes, faces, cc, (b, i) => b.whnf.asInstanceOf[Construct].vs(i)), Seq.empty, Map.empty)
                    }
                  case _: StableCanonical => logicError()
                  case a => null
                }
              } else {
                null
              }
            case u: Universe =>
              null // taken from new cubicaltt, we don't reduce here!
            case Hcomp(u: Universe, b, es) =>
              val wts = es.map((pair: (Formula, AbsClosure)) => {
                val al = pair._1
                val eal = pair._2
                val ret = AbsClosure(i =>
                  transp_inv(Formula.False, eal, hfill(eal( Formula.True), base, faces).apply(i))
                )
                (al, ret)
              })
              val t1s = es.map((pair: (Formula, AbsClosure)) => {
                val al = pair._1
                val eal = pair._2
                val ret = Hcomp(eal(Formula.True), u, faces)
                (al, ret)
              })
              val esmap = es.view.mapValues(a => PathLambda(a)).toMap
              val v = Unglue(b, u, true, esmap)
              val vs = faces.map((pair: (Formula, AbsClosure)) => {
                val al = pair._1
                val ual = pair._2
                val ret = ual.map(v =>
                  Unglue(b, v, true, esmap)
                )
                (al, ret)
              })
              val v1 = Hcomp(b, v, vs ++ wts)
              Glue(v1, t1s)
            case g: GlueType =>
              hcompGlue(g, base, faces)
            case _ => null
          }
      }
      Option(res)
    }
  }

  /**
    * whnf: faces is not constant
    */
  case class GlueType(ty: Value, @stuck_pos faces: ValueSystem) extends UnstableCanonical {
    override def reduceOrSelf() = faces.find(_._1.normalFormTrue).map(b => Projection(b._2, 0)).getOrElse(this)
  }
  /**
    * whnf: faces is not constant
    */
  case class Glue(m: Value, @stuck_pos faces: ValueSystem) extends UnstableCanonical {
    override def reduceOrSelf() = {
      faces.find(_._1.normalFormTrue).map(_._2) match {
        case Some(a) => a
        case None =>
          val bf = m
          bf
//          bf match {
//            case Unglue(b, _, _) => b
//            case _ => this
//          }
      }
    }
  }
  /**
    * whnf: faces is not constant, base is whnf, and base's whnf is not glue
    * LATER this is how the whnf is defined, so glue is considered canonical, but unglue is not
    *
    * FIXME it seems ty can be considered a type annotation? I am confused
    */
  case class Unglue(ty: Value, base: Value, isU: Boolean, @stuck_pos faces: ValueSystem) extends Redux {
    override def reduce(): Option[Value] = logicError() // in whnf
  }

  var NORMAL_FORM_MODEL = false
}

import Value._

sealed trait Value {

  final override def equals(obj: Any): Boolean = (this, obj) match {
    case (r: Value, j: Value) => r.eq(j)
    case _ => logicError()
  }

  def reduceOrSelf(): Value = this

  def reduceUntilSelf() = {
    var old: Value = null
    var b = this
    while ({
      old =b
      b = old.reduceOrSelf()
      b != b
    }) {}
    b
  }


  override def hashCode(): Int = super.hashCode()

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
            if (candidate.referenced != null) {
              val SupportShallow(ns, rs) = candidate.referenced.supportShallow()
              names.addAll(ns)
              toTest.addAll(rs.filterNot(tested))
            } else if (!candidate.isInstanceOf[Value.Generic]) {
              // this is because we use null generic in various cases to look into a closure
              if (candidate.isInstanceOf[Value.Reference]) {
                warn("seems you are defining a recursive value inside a dimension context")
              } else {
                logicError()
              }
            }
          }
      }
    }
    val spt = Support(tested.flatMap {
      case g: Generic => Some(g)
      case _ => None
    }.toSet, names.toSet, tested.flatMap {
      case m@Meta(_: MetaState.Open) => Some(m)
      case _ => None
    }.toSet)
    spt
  }

  def supportShallow(): SupportShallow  = this match {
    case Universe(level) => SupportShallow.empty
    case Function(domain, impict, codomain) => domain.supportShallow() ++ codomain.supportShallow()
    case Lambda(closure) => closure.supportShallow()
    case PatternLambda(id, domain, typ, cases) =>
      domain.supportShallow() ++ typ.supportShallow() ++ cases.map(_.closure.supportShallow()).merge
    case Record(inductively, names, nodes) =>
      inductively.map(_.supportShallow()).orEmpty ++ nodes.supportShallow()
    case Make(values) => values.map(_.supportShallow()).merge
    case Construct(name, vs, ds, ty) =>
      (vs.map(_.supportShallow()) ++ ds.map(_.supportShallow())).merge ++ ty.supportShallow()
    case Sum(inductively, _, constructors) =>
      inductively.map(_.supportShallow()).orEmpty ++ constructors.map(a => a.nodes.supportShallow()).merge
    case PathType(typ, left, right) =>
      typ.supportShallow() ++ left.supportShallow() ++ right.supportShallow()
    case PathLambda(body) => body.supportShallow()
    case App(lambda, argument) => lambda.supportShallow() ++ argument.supportShallow()
    case PatternRedux(lambda, stuck) => lambda.supportShallow() ++ stuck.supportShallow()
    case Projection(make, field) => make.supportShallow()
    case PathApp(left, dimension) => left.supportShallow() +- dimension.names
    case Transp(tp, direction, base) => tp.supportShallow() ++ base.supportShallow() +- direction.names
    case Comp(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ faces.supportShallow()
    case Hcomp(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ faces.supportShallow()
    case GlueType(tp, faces) => tp.supportShallow()++ faces.supportShallow()
    case Glue(base, faces) => base.supportShallow() ++ faces.supportShallow()
    case Unglue(tp, base, iu, faces) => tp.supportShallow() ++ base.supportShallow() ++ faces.supportShallow()
    case referential: Referential => SupportShallow.empty ++ Set(referential)
  }

  /**
    * fresh swap, the id being swapped cannot be used after. this helps because no need for Deswap...
    */
  def fswap(w: Long, z: Formula): Value = this match {
    case u: Universe => u
    case Function(domain, im, codomain) => Function(domain.fswap(w, z), im, codomain.fswap(w, z))
    case Record(inductively, ns, nodes) =>
      Record(inductively.map(_.fswap(w, z)), ns, nodes.fswap(w, z))
    case Make(values) => Make(values.map(_.fswap(w, z)))
    case Construct(name, vs, ds, ty) => Construct(name, vs.map(_.fswap(w, z)), ds.map(_.fswap(w, z)), ty.fswap(w, z))
    case Sum(inductively, hit, constructors) =>
      Sum(inductively.map(_.fswap(w, z)), hit, constructors.map(_.fswap(w, z)))
    case Lambda(closure) => Lambda(closure.fswap(w, z))
    case PatternLambda(id, dom, typ, cases) =>
      PatternLambda(id, dom.fswap(w, z), typ.fswap(w, z), cases.map(a => Case(a.pattern, a.closure.fswap(w, z))))
    case PathType(typ, left, right) =>
      PathType(typ.fswap(w, z), left.fswap(w, z), right.fswap(w, z))
    case PathLambda(body) => PathLambda(body.fswap(w, z))
    case App(lambda, argument) => App(lambda.fswap(w, z), argument.fswap(w, z))
    case t@Transp(tp, direction, base) => Transp(tp.fswap(w, z), direction.fswap(w, z), base.fswap(w, z))
    case h@Hcomp(tp, base, faces) => Hcomp(tp.fswap(w, z), base.fswap(w, z), faces.fswap(w, z))
    case Comp(tp, base, faces) => Comp(tp.fswap(w, z), base.fswap(w, z), faces.fswap(w, z))
    case p@Projection(make, field) => Projection(make.fswap(w, z), field)
    case PatternRedux(lambda, stuck) =>
      PatternRedux(lambda.fswap(w, z).asInstanceOf[PatternLambda], stuck.fswap(w, z))
    case PathApp(left, stuck) => PathApp(left.fswap(w, z), stuck.fswap(w, z))
    case GlueType(base, faces) => GlueType(base.fswap(w, z), faces.fswap(w, z))
    case Glue(base, faces) => Glue(base.fswap(w, z), faces.fswap(w, z))
    case Unglue(tp, base, iu, faces) => Unglue(tp.fswap(w, z), base.fswap(w, z), iu, faces.fswap(w, z))
    case g: Referential => g.getFswap(w, z)
  }



  def restrict(lv: Assignments): Value = if (lv.isEmpty) this else this match {
    case u: Universe => u
    case Function(domain, im, codomain) =>
      Function(domain.restrict(lv), im, codomain.restrict(lv))
    case Record(inductively, ns, nodes) =>
      Record(inductively.map(_.restrict(lv)), ns, nodes.restrict(lv))
    case Make(values) =>
      Make(values.map(_.restrict(lv)))
    case Construct(name, vs, ds, ty) =>
      Construct(name, vs.map(_.restrict(lv)), ds.map(_.restrict(lv)), ty.restrict(lv))
    case Sum(inductively, hit, constructors) =>
      Sum(inductively.map(_.restrict(lv)), hit, constructors.map(_.restrict(lv)))
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
    case t@Transp(tp, direction, base) =>
      Transp(tp.restrict(lv), direction.restrict(lv), base.restrict(lv))
    case h@Hcomp(tp, base, faces) =>
      Hcomp(tp.restrict(lv), base.restrict(lv), faces.restrict(lv))
    case Comp(tp, base, faces) =>
      Comp(tp.restrict(lv), base.restrict(lv), faces.restrict(lv))
    case p@Projection(make, field) =>
      Projection(make.restrict(lv), field)
    case PatternRedux(lambda, stuck) =>
      PatternRedux(lambda.restrict(lv).asInstanceOf[PatternLambda], stuck.restrict(lv))
    case PathApp(left, stuck) =>
      PathApp(left.restrict(lv), stuck.restrict(lv))
    case GlueType(base, faces) =>
      GlueType(base.restrict(lv), faces.restrict(lv))
    case Glue(base, faces) =>
      Glue(base.restrict(lv), faces.restrict(lv))
    case Unglue(tp, base, iu, faces) =>
      Unglue(tp.restrict(lv), base.restrict(lv), iu, faces.restrict(lv))
    case g: Referential =>
      g.getRestrict(lv)
  }


  /**
    *
    *
    *
    *
    *
    *
    *
    * WHNF stuff
    *
    *
    *
    *
    *
    */
  private[Value] var _from: Value = _
  private[Value] var _whnfCache: Value = _


  def bestReifyValue: Value = this match {
    case r: Reference => r
    case Meta(Value.MetaState.Closed(v)) =>
      v match {
        case r: Referential => r.bestReifyValue
        case _ => this
      }
    case v =>
      if (v._from == null) v else v._from
  }


  // it is ensured that if the value is not reducable, it will return the same reference
  def whnf: Value = {
    // TODO don't do this equals stuff!!!
    val cached = _whnfCache
    if (cached == null) {
      val candidate = this match {
        case a: StableCanonical =>
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
        case app@App(lambda, argument) =>
          def app2(lambda: Value, argument: Value): Value = {
            @inline def default() = App(lambda, argument)
            lambda match {
              case Lambda(closure) =>
                closure(argument).whnf
              case p : PatternLambda =>
                PatternRedux(p, argument.whnf).reduceThenWhnfOrSelf()
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
                    @inline def tpr(i: Formula) = tp(i).whnf.asInstanceOf[Function]
                    Transp(
                      AbsClosure(i => tpr(i).codomain(transpFill_inv(i, phi, AbsClosure(j => tpr(j).domain), argument))),
                      phi,
                      App(base, transp_inv(phi, AbsClosure(i => tpr(i).domain), argument))
                    )
                  case _ => default()
                }
              case Comp(tp, base, faces) =>
                // FIXME what about comp in cubicaltt? it seems it is not essential
                default()
              case _: StableCanonical => logicError()
              case _ =>
                default()
            }
          }
          app2(lambda.whnf, argument) match {
            case App(l2, a2) if lambda == l2 && a2 == argument => this
            case a => a
          }
        case pat@PatternRedux(lambda, stuck) =>
          PatternRedux(lambda, stuck.whnf).reduceThenWhnfOrSelf() match {
            case PatternRedux(l2, s2) if lambda == l2 && stuck == s2 => this
            case a => a
          }
        case pro@Projection(make, field) =>
          Projection(make.whnf, field).reduceThenWhnfOrSelf() match {
            case Projection(m2, f2) if make == m2 && field == f2 => this
            case a => a
          }
        case c@Construct(f, vs, ds, ty) =>
          if (ds.isEmpty) {
            c
          } else {
            ty.find(_._1.normalFormTrue) match {
              case Some(value) => value._2.whnf
              case None => c
            }
          }
        case PathApp(left, dimension) =>
          // we MUST perform this, because this doesn't care
          PathApp(left.whnf, dimension).reduceThenWhnfOrSelf() match {
            case PathApp(l2, s2) if left == l2 && dimension == s2 => this
            case a => a.whnf
          }
        case transp@Transp(direction, tp, base) =>
          // kan ops case analysis on tp, so they perform their own whnf
          transp.reduceThenWhnfOrSelf() match {
            case Transp(d2, t2, b2) if d2 == direction && t2 == tp && base == b2 => this
            case a => a
          }
        case com@Comp(tp, base, faces) =>
          com.reduceThenWhnfOrSelf() match {
            case Comp(t2, b2, f2) if tp == t2 && base == b2 && faces == f2 => this
            case a => a
          }
        case hcom@Hcomp(tp, base, faces) =>
          Hcomp(tp.whnf, base, faces).reduceThenWhnfOrSelf() match {
            case Hcomp(t2, b2, f2) if tp == t2 && base == b2 && faces == f2 => this
            case a => a
          }
        case GlueType(tm, faces) =>
          faces.find(_._1.normalFormTrue).map(b => Projection(b._2, 0).whnf).getOrElse(this)
        case Glue(base, faces) =>
          faces.find(_._1.normalFormTrue).map(_._2.whnf) match {
            case Some(a) => a
            case None =>
              val bf = base.whnf
              if (bf == base) this else Glue(bf, faces)
          }
        case Unglue(ty, base, iu, faces) =>
          val red = faces.find(_._1.normalFormTrue).map(b =>
            if (iu) transp_inv(Formula.False, b._2.whnf.asInstanceOf[PathLambda].body, base).whnf
            else App(Projection(Projection(b._2, 1), 0), base).whnf)
          red match {
            case Some(a) => a
            case None =>
              val bf = base.whnf
              bf match {
                case Glue(b, _) => b.whnf
                case _ =>
                  this // FIXME to see what's inside
                  // if (bf == base) this else Unglue(ty, bf, iu, faces)
              }
          }
      }
      if (Value.NORMAL_FORM_MODEL) {
        _whnfCache = candidate
      }
      //} else {
        // because some values is shared, it means the solved ones is not created for this whnf, we don't say this
        // is from us
        // TODO these are already defined ones, think more about this
        if (candidate == this) { // this is a terminal form, it has no from now
        } else {
          var c = candidate
          if (c._from == null) {
            c._from = this
          }
        }
        candidate
      //}
    } else {
      cached
    }
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
        r.inductively.map(_.typFinal).getOrElse(Universe(r.nodes.inferLevel()))
      case s: Sum =>
        s.inductively.map(_.typFinal).getOrElse(
          Universe(if (s.constructors.isEmpty) 0 else s.constructors.map(c => c.nodes.inferLevel()).max))
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
      case Unglue(ty, _, _, _) => ty
      case _ => logicError()
    }
  }


  def demeta(): Value = this match {
    case Meta(c: MetaState.Closed) => c.v.demeta()
    case _ => this
  }

  def deref(): Value = this match {
    case r: Reference => r.value.deref()
    case Meta(c: MetaState.Closed) => c.v.deref()
    case _ => this
  }
}
