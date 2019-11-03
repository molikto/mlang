package mlang.compiler

import mlang.compiler.Abstract._
import mlang.compiler.Layer.Layers
import mlang.compiler.Value.{ClosureGraph, Meta, MetaState}
import mlang.utils.{Benchmark, Name, debug}

import scala.collection.mutable


// FIXME this implicitly uses positive generated ids, also unification, becasue they modify the layers, this is not a problem because we don't use positive/negative difference, but it defeats the design
private trait ReifierContext extends ElaboratorContextBuilder with ElaboratorContextRebind {
  def base: ReifierContextBottom

  override type Self <: ReifierContext

  val metas = mutable.ArrayBuffer.empty[Abstract]

  protected def reifyMetas(): Seq[Abstract] = {
    val res = metas.toSeq.drop(layers.head.metas.freezeSize)
    freeze()
    res
  }

  def reifyReference(r: Value.Reference): Abstract.Reference = {
    rebindReference(r) match {
      case Some(t) => t
      case None =>
        base.saveOutOfScopeValue(r)
        rebindReference(r).get
    }
  }


  def reify(graph0: Value.ClosureGraph): Abstract.ClosureGraph = {
    var ctx: ReifierContext = newParametersLayer()
    var graph = graph0
    var as =  Seq.empty[Abstract.ClosureGraph.Node]
    for (i  <- graph0.graph.indices) {
      val n = graph(i)
      val it = n.independent.typ
      val ttt = ctx.reify(it)
      val pair = Abstract.ClosureGraph.Node(n.implicitt, n.dependencies, Abstract.MetaEnclosed(ctx.reifyMetas(), ttt))
      as = as :+ pair
      val (ctx0, tm) = ctx.newParameter(Name.empty, null)
      ctx = ctx0
      graph = graph.reduce(i, tm)
    }
    if (graph0.dimSize == 0) {
      Abstract.ClosureGraph(as, 0, Map.empty)
    } else {
      val ds = (0 until graph0.dimSize).map(_ => {
        val (ctx0, d) = ctx.newDimension(Name.empty)
        ctx = ctx0
        d
      })
      val ms = graph.reduce(ds).restrictions().toSeq.map(r => {
        (ctx.reify(r._1), {
          val ctx0 = ctx.newReifierRestrictionLayer(r._1)
          val vv = ctx0.reify(r._2)
          Abstract.MetaEnclosed(ctx0.reifyMetas(), vv)
        })
      }).toMap
      Abstract.ClosureGraph(as, graph0.dimSize, ms)
    }
  }

  def reify(v: Value.Closure): Abstract.Closure = {
    val (ctx, tm) = newParameterLayer(Name.empty, null)
    val ta = ctx.reify(v(tm))
    Abstract.Closure(ctx.reifyMetas(), ta)
  }

  def reifyMetaEnclosed(v: Value): Abstract.MetaEnclosed = {
    val ctx = newDefinesLayer()
    val ta = ctx.reify(v)
    Abstract.MetaEnclosed(ctx.reifyMetas(), ta)
  }

  def reify(v: Value.AbsClosure): Abstract.AbsClosure = {
    val (ctx, tm) = newDimensionLayer(Name.empty)
    val ta = ctx.reify(v(tm))
    Abstract.AbsClosure(ctx.reifyMetas(), ta)
  }

  def mkContext(size: (Int, Int)) = {
    var ctx = newParametersLayer().asInstanceOf[ReifierContext]
    var vs = mutable.ArrayBuffer[Value]()
    val ds = mutable.ArrayBuffer[Value.Formula]()
    for (_ <- 0 until size._1) {
      val (ctx0, v) = ctx.newParameter(Name.empty, null)
      ctx = ctx0
      vs.append(v)
    }
    for (_ <- 0 until size._2) {
      val (ctx0, v) = ctx.newDimension(Name.empty)
      ctx = ctx0
      ds.append(v)
    }
    (ctx, vs.toSeq, ds.toSeq)
  }

  def reify(size: (Int, Int), v: Value.MultiClosure): Abstract.MultiClosure = {
    val (ctx, vs, ds) = mkContext(size)
    val ta = ctx.reify(v(vs, ds))
    Abstract.MultiClosure(ctx.reifyMetas(), ta)
  }

  def reify(id: Option[Value.Inductively]): Option[Inductively] = {
    id match {
      case Some(value) => Some(Inductively(value.id, reify(value.typ), value.ps.map(reify)))
      case None => None
    }
  }

  def reifyAbsClosureSystem(faces: Value.AbsClosureSystem) =
    if (faces.isEmpty) Map.empty : Abstract.AbsClosureSystem else faces.toSeq.map(r => (reify(r._1), newReifierRestrictionLayer(r._1).reify(r._2))).toMap

  def reifyEnclosedSystem(faces: Value.ValueSystem) =
    if (faces.isEmpty) Map.empty : Abstract.EnclosedSystem else faces.toSeq.map(r => (reify(r._1), newReifierRestrictionLayer(r._1).reifyMetaEnclosed(r._2))).toMap


  def reify(v: Value): Abstract = {
    v match {
      case Value.Universe(level) =>
        Universe(level)
      case Value.Function(domain, i, codomain) =>
        Function(reify(domain), i, reify(codomain))
      case Value.Record(id, names, nodes) =>
        Record(reify(id), names, reify(nodes))
      case Value.Sum(id, hit, constructors) =>
        // TODO, you should be able to read the code directly from context
        Sum(reify(id), hit, constructors.map(c => Constructor(c.name, reify(c.nodes))))
      case Value.PathType(ty, left, right) =>
        PathType(reify(ty), reify(left), reify(right))
      case Value.Lambda(closure) =>
        Lambda(reify(closure))
      case Value.PatternLambda(id, dom, ty, cases) =>
        PatternLambda(id, reify(dom), reify(ty), cases.map(c => Case(c.pattern, reify(c.pattern.atomCount, c.closure))))
      case Value.PathLambda(body) =>
        PathLambda(reify(body))
      case m: Value.Meta =>
        m.state match {
          case MetaState.Closed(c) =>
            rebindMetaOpt(m) match {
              case Some(k) => k
              case None =>
                // TODO [issue 2] add to the level where it can be defined with minimal dependency
                // find proper level, and use `Abstract.diff` to correct the dbi
                metas.append(reify(c))
                solvedMeta(m)
            }
          case _: MetaState.Open =>
            rebindOrAddMeta(m)
        }
      case g: Value.Generic =>
        rebindGeneric(g)
      case c: Value.Reference =>
        reifyReference(c)
      case Value.App(lambda, argument) =>
        App(reify(lambda), reify(argument))
      case Value.Projection(make, field) =>
        Projection(reify(make), field)
      case Value.PatternRedux(lambda, stuck) =>
        App(reify(lambda), reify(stuck))
      case Value.Make(vs) =>
        Make(vs.map(reify))
      case Value.Construct(f, vs, ds, ty) =>
        Construct(f, vs.map(reify), ds.map(reify), reifyEnclosedSystem(ty))
      case Value.PathApp(left, stuck) =>
        PathApp(reify(left), reify(stuck))
      case Value.Transp(tp, dir, base) =>
        Transp(reify(tp), reify(dir), reify(base))
      case Value.Hcomp(tp, base, faces) =>
        Hcomp(reify(tp), reify(base), reifyAbsClosureSystem(faces))
      case Value.Comp(tp, base, faces) =>
        Comp(reify(tp), reify(base), reifyAbsClosureSystem(faces))
      case Value.GlueType(ty, faces) =>
        GlueType(reify(ty), reifyEnclosedSystem(faces))
      case Value.Glue(base, faces) =>
        Glue(reify(base), reifyEnclosedSystem(faces))
      case Value.Unglue(ty, base, iu, faces) =>
        Unglue(reify(ty), reify(base), iu, reifyEnclosedSystem(faces))
    }
  }

  def reify(a: Value.Formula): Abstract.Formula = {
    rebindFormula(a)
  }
}

private class ReifierContextCont(override val base: ReifierContextBottom, override val layers: Layers) extends ReifierContext {
  override type Self = ReifierContextCont
  override protected implicit def create(a: Layers): ReifierContextCont = new ReifierContextCont(base, a)
}

// this is the context of the let expression where out-of-scope reference is collected
// FIXME the logic is wrong for local let expression, because we removed the logic to have let values in Value... also rewrite the reifyFaces stuff
private class ReifierContextBottom(layersBefore: Layers) extends ReifierContext {

  private val terms = new mutable.ArrayBuffer[DefineItem]()
  private var data = Seq.empty[(Int, Option[Abstract])]
  private val ms = createMetas()
  override protected def layers: Layers = Layer.Defines(ms, terms.toSeq) +: layersBefore

  private var self: Value = _


  def saveOutOfScopeValue(r: Value.Reference): Unit = {
    val index = terms.size
    debug(s"out of scope value saved??", 2)
    terms.append(DefineItem(ParameterBinder(Name.empty, Value.Generic(GenLong.Negative.gen(), null)), Some(r)))
    val abs = if (r.value.eq(self)) {
      None : Option[Abstract]
    } else {
      Some(reify(r.value))
    }
    val k = (index, abs)
    data = data :+ k
  }

  def reifyValue(v: Value): Abstract = {
    self = v
    val body = reify(v)
    val c = data.count(_._2.isEmpty)
    assert(c <= 1)
    val abs = data.sortBy(_._1).map(_._2.getOrElse(body))
    val ms = reifyMetas()
    if (c == 1) {
      Let(ms, abs, Reference(0, data.find(_._2.isEmpty).get._1))
    } else {
      if (ms.isEmpty && abs.isEmpty) {
        body.diff(0, -1)
      } else {
        Let(ms, abs, body)
      }
    }
  }

  override def base: ReifierContextBottom = this
  override type Self = ReifierContextCont
  override protected implicit def create(a: Layers): ReifierContextCont = new ReifierContextCont(this, a)
}

object Reifier {
  private def reify(v: Value, layers: Seq[Layer]): Abstract = Benchmark.Reify { new ReifierContextBottom(layers).reifyValue(v)  }
}
trait Reifier extends ElaboratorContextBuilder with ElaboratorContextRebind {

  protected def reify(v: Value): Abstract = Reifier.reify(v, layers)

  // FIXME the logic for base/top reify is confusing, try clean them up
  protected def reify(v: Value.Closure): Abstract.Closure = {
    val l = debug_metasSize
    val (c, t) = newParameterLayer(Name.empty, null)
    val r = Abstract.Closure(Seq.empty, c.asInstanceOf[Reifier].reify(v(t)))
    assert(debug_metasSize == l) // we don't create meta in current layer!
    assert(c.debug_metasSize == 0) // also we don't create in that one!
    r
  }

  protected def reifyEnclosedSystem(v: Value.ValueSystem): Abstract.EnclosedSystem = {
    v.map(f => {
      (rebindFormula(f._1),  {
        val l = debug_metasSize
        val c = newReifierRestrictionLayer(f._1).newParametersLayer()
        val r = Abstract.MetaEnclosed(Seq.empty, c.asInstanceOf[Reifier].reify(f._2))
        assert(debug_metasSize == l) // we don't create meta in current layer!
        assert(c.debug_metasSize == 0) // also we don't create in that one!
        r
      })
    })
  }

  protected def freezeReify(): Seq[Abstract] = {
    val vs = freeze()
    vs.map(a => reify(a.solved))
  }

  protected def finishReify(): Seq[Abstract] = {
    val vs = finish()
    vs.map(a => reify(a.solved))
  }

}
