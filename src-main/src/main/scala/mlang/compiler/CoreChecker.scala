package mlang.compiler

import dbi.Abstract
import semantic.{Value, ValueConversion}
import mlang.utils._
import mlang.compiler.semantic.{Value, ValueConversion, MetaSpine, MetaState}

import scala.collection.mutable


case class CoreCheckFailedException() extends CompilerException
case class CannotSolveMetaDuringCoreChecking() extends CompilerException

object CoreCheckerConversion extends ValueConversion {
  val Phase = Benchmark.CoreConversion
  override protected def trySolve(m: Value.Meta, vs: MetaSpine, t20: Value): Option[Value] = throw CannotSolveMetaDuringCoreChecking()
}

// FIXME(META) very very simple and non-complete checker!! it dones't handles all cases possible
trait CoreChecker extends ElaboratorContextBuilder
  with ElaboratorContextLookup
  with ElaboratorContextRebind
  with ElaboratorContextForEvaluator
  with ElaboratorContextWithMetaOps
  with Evaluator {

  type Self  <: CoreChecker
  // FIXME(META) the trait system seems to make core check solving metas in it's way, consider if it is ok

  def newLocalMetas(abs: Seq[Abstract]): Self = {
    abs.foreach(a => {
      val t = cinfer(a)
      solvedMeta(Value.LocalMeta.solved(eval(a)), t, a)
    })
    this.asInstanceOf[Self]
  }

  def cinferLevel(abs: Abstract): Int = {
    cinfer(abs).whnf match {
      case Value.Universe(l) => l
      case _ => logicError()
    }
  }

  def cinfer(abs: Abstract): Value = {
    abs match {
      case Abstract.Reference(up, index, lvl) =>
        getReferenceType(up, index, lvl)
      case Abstract.MetaReference(up, index, lvl) =>
         getMetaReferenceType(up, index, lvl)
      case Abstract.Universe(i) =>
        Value.Universe.suc(i)
      case Abstract.Function(d, i, co) =>
        val u1 = cinferLevel(d)
        val (ctx, gen) = newParameterLayer(Name.empty, eval(d))
        val u2 = ctx.newLocalMetas(co.metas).cinferLevel(co.term)
        Value.Universe(u1 max u2)
      case Abstract.Record(ind, ns, gs) =>
        ???
      case Abstract.Sum(ind, ht, cs) =>
        ???
      case Abstract.GlueType(tp, pos) =>
        ???
      case Abstract.PathType(tp, left, right) =>
        val (ctx, gen) = newDimensionLayer(Name.empty)
        ctx.newLocalMetas(tp.metas).cinfer(tp.term)
      case Abstract.PathApp(a, b) =>
        cinfer(a).whnf match {
          case Value.PathType(ty, _, _) => ty(eval(b))
          case _ => logicError()
        }
      case Abstract.Projection(a, b) =>
        cinfer(a).whnf match {
          case s: Value.Record => s.projectedType(eval(a), b)
          case _ => logicError()
        }
      case Abstract.Let(ms, ds, in) =>
        if (ds.isEmpty) {
          newParametersLayer().newLocalMetas(ms).cinfer(in)
        } else {
          ???
        }
      case Abstract.App(a, b) =>
        cinfer(a).whnf match {
          case Value.Function(d, i, co) =>
            co(eval(b))
          case _ => logicError()
        }
      case _ =>
        ???
    }
  }


  def ccheck(vs: Seq[Abstract], ds: Seq[dbi.Formula], ty: dbi.System, nodes: semantic.ClosureGraph): Unit = {
    // FIXME(META) should you also check ty and ds?
    if (ds.size == nodes.dimSize && vs.size == nodes.size) {
      var ns = nodes
      val vvs = mutable.ArrayBuffer[Value]()
      for (i <- 0 until vs.size) {
        ccheck(vs(i), ns.get(i, vvs))
        val ddd = eval(vs(i))
        vvs.append(ddd)
        ns = ns.reduce(i, ddd)
      }
    } else {
      logicError()
    }
  }
  def check(abs: Abstract, to: Value): Unit = Benchmark.CoreChecker {
    ccheck(abs, to)
  }

  private def ccheck(abs: Abstract, to: Value): Unit = {
    abs match {
      case Abstract.Let(ms, ds, in) =>
        if (ds.isEmpty) {
          newParametersLayer().newLocalMetas(ms).ccheck(in, to)
        } else {
          ???
        }
      case Abstract.Lambda(closure) =>
        to.whnf match {
          case Value.Function(d, _, co) =>
            val (ctx, gen) = newParameterLayer(Name.empty, d)
            ctx.newLocalMetas(closure.metas).ccheck(closure.term, co(gen))
          case _ => logicError()
        }
      case Abstract.Make(vs) =>
        to.whnf match {
          case Value.Record(ind, _, nodes) =>
            ccheck(vs, Seq.empty, Map.empty, nodes)
          case _ => logicError()
        }
      case Abstract.Construct(f, vs, ds, ty) =>
        to.whnf match {
          case Value.Sum(ind, hit, cons) =>
            if (f < cons.size) {
              ccheck(vs, ds, ty, cons(f).nodes)
            } else {
              logicError()
            }
          case _ => logicError()
        }
      case _ =>
        val left = cinfer(abs)
        if (!CoreCheckerConversion.subTypeOf(left, to)) {
          throw CoreCheckFailedException()
        }
    }
  }
}