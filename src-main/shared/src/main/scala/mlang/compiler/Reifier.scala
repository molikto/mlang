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

  protected def reifyMetas(): Seq[Abstract] = metas.toSeq

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
    var as =  Seq.empty[(Seq[Int], MetaEnclosed)]
    for (i  <- graph0.indices) {
      val n = graph(i)
      val it = n.independent.typ
      val ttt = ctx.reify(it)
      val pair = (n.dependencies, Abstract.MetaEnclosed(ctx.reifyMetas(), ttt))
      as = as :+ pair
      val (ctx0, tm) = ctx.newParameter(Name.empty, null)
      ctx = ctx0
      graph = ClosureGraph.reduce(graph, i, tm)
    }
    as
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

  def reify(size: Int, v: Value.MultiClosure): Abstract.MultiClosure = {
    val (ctx, ns) = (0 until size).foldLeft((newParametersLayer() : ReifierContext, Seq.empty[Value])) { (ctx, _) =>
      val (c, ns) = ctx._1.newParameter(Name.empty, null)
      (c, ctx._2 :+ ns)
    }
    val ta = ctx.reify(v(ns))
    Abstract.MultiClosure(ctx.reifyMetas(), ta)
  }

  def reify(id: Option[Value.Inductively]): Option[Inductively] = {
    id match {
      case Some(value) => Some(Inductively(value.id, value.level))
      case None => None
    }
  }

  def reifyFaces(faces: Seq[Value.Face]) =
    faces.map(r => Face(reify(r.restriction), newReifierRestrictionLayer(r.restriction).reify(r.body)))

  def reify(v: Value): Abstract = {
    v match {
      case Value.Universe(level) =>
        Universe(level)
      case Value.Function(domain, i, codomain) =>
        Function(reify(domain), i, reify(codomain))
      case Value.Record(id, names, is, nodes) =>
        Record(reify(id), names, is, reify(nodes))
      case Value.Sum(id, constructors) =>
        Sum(reify(id), constructors.map(c => Constructor(c.name, c.ims, reify(c.nodes))))
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
      case Value.Construct(f, vs) =>
        Construct(f, vs.map(reify))
      case Value.PathApp(left, stuck) =>
        PathApp(reify(left), reify(stuck))
      case Value.Transp(tp, dir, base) =>
        Transp(reify(tp), reify(dir), reify(base))
      case Value.Hcomp(tp, base, faces) =>
        Hcomp(reify(tp), reify(base), reifyFaces(faces))
      case Value.Comp(tp, base, faces) =>
        Comp(reify(tp), reify(base), reifyFaces(faces))
      case Value.GlueType(ty, faces) =>
        GlueType(reify(ty), reifyFaces(faces))
      case Value.Glue(base, faces) =>
        Glue(reify(base), reifyFaces(faces))
      case Value.Unglue(ty, base, faces) =>
        Unglue(reify(ty), reify(base), reifyFaces(faces))
      case _: Value.Internal =>
        logicError()
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

  protected def reifyFaces(v: Seq[Value.Face]): Seq[Abstract.Face] = {
    v.map(f => {
      Abstract.Face(rebindFormula(f.restriction),  {
        val l = debug_metasSize
        val (c, t) = newReifierRestrictionLayer(f.restriction).newDimensionLayer(Name.empty)
        val r = Abstract.AbsClosure(Seq.empty, c.asInstanceOf[Reifier].reify(f.body(t)))
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
