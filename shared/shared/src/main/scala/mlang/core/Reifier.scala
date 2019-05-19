package mlang.core

import mlang.core.Abstract._
import mlang.core.Context.Layers
import mlang.core.Value.ClosureGraph
import mlang.name.Name
import mlang.utils.Benchmark

import scala.collection.mutable



private trait ReifierContext extends ContextBuilder {
  def base: ReifierContextBase

  override type Self <: ReifierContext

  def reifyReference(r: Value.Reference): Abstract.Reference = {
    rebindReference(r) match {
      case Some(t) => t
      case None =>
        base.saveOutOfScopeValue(r)
        rebindReference(r).get
    }
  }

  def reify(graph0: Value.ClosureGraph): Abstract.ClosureGraph = {
    val (ctx, vs0) = graph0.foldLeft((newParametersLayer().asInstanceOf[ReifierContext], Seq.empty[Value])) { (as, _) =>
      val (cc, v) = as._1.newParameter(Name.empty, null)
      (cc, as._2 :+ v)
    }
    assert(vs0.size == graph0.size)
    var graph = graph0
    var as =  Seq.empty[(Seq[Int], Abstract)]
    for (i  <- graph0.indices) {
      val n = graph(i)
      val it = n.independent.typ
      val pair = (n.dependencies, ctx.reify(it))
      as = as :+ pair
      graph = ClosureGraph.reduce(graph, i, vs0(i))
    }
    as
  }

  def reify(v: Value): Abstract = {
    v match {
      case Value.Universe(level) =>
        Universe(level)
      case Value.Function(domain, codomain) =>
        val (ctx, tm) = newParameterLayer(Name.empty, domain)
        Function(reify(domain), ctx.reify(codomain(tm)))
      case Value.Record(level, names, nodes) =>
        Record(level, names, reify(nodes))
      case Value.Sum(level, constructors) =>
        Sum(level, constructors.map(c => {
          Constructor(c.name, reify(c.nodes))
        }))
      case Value.PathType(ty, left, right) =>
        val (ctx, d) = newDimensionLayer(Name.empty)
        PathType(ctx.reify(ty(d)), reify(left), reify(right))
      case Value.Make(_) =>
        // we believe at least values from typechecker don't have these stuff
        // we can extends it when time comes
        logicError()
      case Value.Construct(_, _) =>
        logicError()
      case Value.Lambda(closure) =>
        val (ctx, n) = newParameterLayer(Name.empty, null)
        Lambda(ctx.reify(closure(n)))
      case Value.PatternLambda(id, ty, cases) =>
        val (ctx, n) = newParameterLayer(Name.empty, null)
        PatternLambda(id, ctx.reify(ty(n)), cases.map(c => {
          val (ctx, ns) = (0 until c.pattern.atomCount).foldLeft((newParametersLayer().asInstanceOf[ReifierContext], Seq.empty[Value])) { (ctx, _) =>
            val (c, ns) = ctx._1.newParameter(Name.empty, null)
            (c, ctx._2 :+ ns)
          }
          Case(c.pattern, ctx.reify(c.closure(ns)))
        }))
      case Value.PathLambda(body) =>
        val (ctx, n) = newDimensionLayer(Name.empty)
        PathLambda(ctx.reify(body(n)))
      case Value.Generic(id, _) =>
        rebindGeneric(id)
      case c: Value.Reference =>
        reifyReference(c)
      case Value.App(lambda, argument) =>
        App(reify(lambda), reify(argument))
      case Value.Projection(make, field) =>
        Projection(reify(make), field)
      case Value.PatternStuck(lambda, stuck) =>
        App(reify(lambda), reify(stuck))
      case Value.Maker(s, i) =>
        Maker(reify(s), i)
      case Value.Let(items, order, body) =>
        val ctx = items.foldLeft(newDefinesLayer().asInstanceOf[ReifierContext]) { (ctx, item) =>
          ctx.newDefinition(Name.empty, null, item)
        }
        val abs = items.map(p => ctx.reify(p))
        Let(abs, order, ctx.reify(body))
      case Value.PathApp(left, stuck) =>
        PathApp(reify(left), reify(stuck))
      case Value.Coe(dir, tp, base) =>
        val (ctx, n) = newDimensionLayer(Name.empty)
        Coe(reify(dir), ctx.reify(tp(n)), reify(base))
      case Value.Hcom(dir, tp, base, faces) =>
        val (ctx, n) = newParametersLayer().newDimensionLayer(Name.empty)
        Hcom(reify(dir), reify(tp), reify(base), faces.map(r => Face(reify(r.restriction), ctx.reify(r.body(n)))))
      case Value.Com(dir, tp, base, faces) =>
        Com(reify(dir), {
          val (ctx, n) = newDimensionLayer(Name.empty)
          ctx.reify(tp(n))
        }, reify(base), {
          val (ctx, n) = newParametersLayer().newDimensionLayer(Name.empty)
          faces.map(r => Face(reify(r.restriction), ctx.reify(r.body(n))))
        })
      case Value.Restricted(a, pair) =>
        pair.foldLeft(reify(a)) { (c, p) =>
          Restricted(c, reify(p))
        }
    }
  }

  def reify(a: Value.DimensionPair): Abstract.DimensionPair = {
    Abstract.DimensionPair(reify(a.from), reify(a.to))
  }

  def reify(a: Value.Dimension): Abstract.Dimension = {
    rebindDimension(a)
  }
}

private class ReifierContextCont(override val base: ReifierContextBase, override val layers: Context.Layers) extends ReifierContext {
  def gen: LongGen.Negative = base.gen

  override type Self = ReifierContextCont
  override protected implicit def create(a: Layers): ReifierContextCont = new ReifierContextCont(base, a)
}

// this is the context of the let expression where out-of-scope reference is collected
private class ReifierContextBase(layersBefore: Context.Layers) extends ReifierContext {
  private val terms = new mutable.ArrayBuffer[DefineItem]()
  private var data = Seq.empty[(Int, Option[Abstract])]
  override protected val layers: Layers =  Layer.Defines(createMetas(), terms) +: layersBefore

  private var self: Value = _


  def saveOutOfScopeValue(r: Value.Reference): Unit = {
    val index = terms.size
    terms.append(DefineItem(ParameterBinder(0, Name.empty, null), Some(r.value)))
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
    val order = data.map(_._1)
    val abs = data.sortBy(_._1).map(_._2.getOrElse(body))
    if (c == 1) {
      Let(abs, order, Reference(0, data.find(_._2.isEmpty).get._1, true))
    } else {
      Let(abs, order, body)
    }
  }

  override def base: ReifierContextBase = this
  val gen = new LongGen.Negative()
  override type Self = ReifierContextCont
  override protected implicit def create(a: Layers): ReifierContextCont = new ReifierContextCont(this, a)

}

trait Reifier extends Context {
  def reify(v: Value): Abstract = Benchmark.Reify { new ReifierContextBase(layers).reifyValue(v) }
}
