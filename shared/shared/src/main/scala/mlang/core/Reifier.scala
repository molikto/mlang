package mlang.core

import mlang.core.Abstract._
import mlang.core.Context.Layers
import mlang.core.Value.{ClosureGraph, Meta}
import mlang.name.Name
import mlang.utils.Benchmark

import scala.collection.mutable


private trait ReifierContext extends ContextBuilder {
  def base: ReifierContextBase

  override type Self <: ReifierContext


  val metas = mutable.ArrayBuffer.empty[Abstract]


  protected def reifyMetas(): Seq[Abstract] = metas

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

  def reify(v: Value.AbsClosure): Abstract.AbsClosure = {
    val (ctx, tm) = newDimensionLayer(Name.empty, None)
    val ta = ctx.reify(v(tm))
    Abstract.AbsClosure(ctx.reifyMetas(), ta)
  }

  def reify(size: Int, v: Value.MultiClosure): Abstract.MultiClosure = {
    val (ctx, ns) = (0 until size).foldLeft((newParametersLayer().asInstanceOf[ReifierContext], Seq.empty[Value])) { (ctx, _) =>
      val (c, ns) = ctx._1.newParameter(Name.empty, null)
      (c, ctx._2 :+ ns)
    }
    val ta = ctx.reify(v(ns))
    Abstract.MultiClosure(ctx.reifyMetas(), ta)
  }

  def reify(id: Option[Value.Inductively]): Option[Inductively] = {
    id match {
      case Some(value) => Some(Inductively(value.id))
      case None => None
    }
  }

  def reify(v: Value): Abstract = {
    v match {
      case Value.Universe(level) =>
        Universe(level)
      case Value.Up(t, i) =>
        Up(reify(t), i)
      case Value.Function(domain, i, codomain) =>
        Function(reify(domain), i, reify(codomain))
      case Value.Record(level, id, names, is, nodes) =>
        Record(level, reify(id), names, is, reify(nodes))
      case Value.Sum(level, id, constructors) =>
        Sum(level, reify(id), constructors.map(c => Constructor(c.name, c.ims, reify(c.nodes))))
      case Value.PathType(ty, left, right) =>
        PathType(reify(ty), reify(left), reify(right))
      case Value.Make(_) =>
        // we believe at least values from typechecker don't have these stuff
        // we can extends it when time comes
        logicError()
      case Value.Construct(_, _) =>
        logicError()
      case Value.Lambda(closure) =>
        Lambda(reify(closure))
      case Value.PatternLambda(id, ty, cases) =>
        PatternLambda(id, reify(ty), cases.map(c => Case(c.pattern, reify(c.pattern.atomCount, c.closure))))
      case Value.PathLambda(body) =>
        PathLambda(reify(body))
      case m: Value.Meta =>
        m.v match {
          case Meta.Closed(c) =>
            rebindMetaOpt(m) match {
              case Some(k) => k
              case None =>
                // TODO [issue 2] add to the level where it can be defined with minimal dependency
                // find proper level, and use `Abstract.diff` to correct the dbi
                metas.append(reify(c))
                solvedMeta(m)
            }
          case _: Meta.Open =>
            rebindOrAddMeta(m)
        }
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
      case Value.Let(items, body) =>
        val ctx = items.foldLeft(newDefinesLayer().asInstanceOf[ReifierContext]) { (ctx, item) =>
          ctx.newDefinition(Name.empty, null, Value.Reference(item))._1
        }
        val abs = items.map(p => ctx.reify(p))
        val bd = ctx.reify(body)
        Let(ctx.reifyMetas(), abs, bd)
      case Value.PathApp(left, stuck) =>
        PathApp(reify(left), reify(stuck))
      case Value.Coe(dir, tp, base) =>
        Coe(reify(dir), reify(tp), reify(base))
      case Value.Hcom(dir, tp, base, faces) =>
        Hcom(reify(dir), reify(tp), reify(base), faces.map(r => Face(reify(r.restriction), reify(r.body))))
      case Value.Com(dir, tp, base, faces) =>
        Com(reify(dir), reify(tp), reify(base),
          faces.map(r => Face(reify(r.restriction), newRestrictionLayer(r.restriction).reify(r.body)))
        )
      case Value.Restricted(a, pair) =>
        Restricted(reify(a), pair.map(k => reify(k)))
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
    terms.append(DefineItem(ParameterBinder(Name.empty, null), Some(r)))
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

  override def base: ReifierContextBase = this
  val gen = new LongGen.Negative()
  override type Self = ReifierContextCont
  override protected implicit def create(a: Layers): ReifierContextCont = new ReifierContextCont(this, a)

}

object Reifier {
  private def reify(v: Value, layers: Seq[Layer]): Abstract = Benchmark.Reify { new ReifierContextBase(layers).reifyValue(v)  }
}
trait Reifier extends ContextBuilder {

  protected def reify(v: Value): Abstract = Reifier.reify(v, layers)


  protected def reify(v: Value.Closure): Abstract.Closure = {
    val l = debug_metasSize
    val (c, t) = newParameterLayer(Name.empty, null)
    val r = Abstract.Closure(Seq.empty, c.asInstanceOf[Reifier].reify(v(t)))
    assert(debug_metasSize == l) // we don't create meta in current layer!
    assert(c.debug_metasSize == 0) // also we don't create in that one!
    r
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
