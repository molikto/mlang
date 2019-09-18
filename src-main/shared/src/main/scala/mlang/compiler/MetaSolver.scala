package mlang.compiler

import Value.{Reference => _, _}
import mlang.utils.{Benchmark, Name, debug, warn}

import scala.collection.mutable
import scala.util.{Failure, Success, Try}
import GenLong.Negative.{gen, dgen}



case class UnificationFailedException(msg: String) extends Exception

trait MetaSolver extends ValueConversion with Reifier with ElaboratorContextRebind with Evaluator {

  type Self  <: MetaSolver

  private def error(s: String) = throw UnificationFailedException(s)

  protected def trySolve(m: Meta, vs: Seq[Value], t20: Value): Option[Value] = {
    Try(solve(m, vs, t20)) match {
      case Failure(exception) =>
        if (debug.enabled) {
          exception.printStackTrace()
        }
        exception match {
          case _: UnificationFailedException =>
            unifyFailed()
          case _: RebindNotFoundException =>
            unifyFailed()
          case e => throw e
        }
      case Success(v) =>
        Some(v)
    }
  }

  private def solve(m: Meta, vs: Seq[Value], t20: Value): Value = Benchmark.Solve {
    var MetaState.Open(_, typ) = m.state.asInstanceOf[MetaState.Open]
    val ref = rebindMeta(m)
    var ctx = drop(ref.up) // back to the layer where the meta is introduced
    val index = ref.index
    val os = vs.map {
      case o: Generic => o
      case _ => error("Spine is not generic")
    }
    val gs = os.map(_.id)
    for (i <- gs.indices) {
      val o = os(i)
      if (ctx.containsGeneric(o)) error("Spine is not linear")
      ctx = ctx.newParameterLayerProvided(Name.empty, o).asInstanceOf[Self]
    }
    val t2 = t20.bestValue // FIXME is this sound??
    if (t2.support().openMetas.contains(m)) {
      error("Meta solution contains self")
    }
    // this might throw error if scope checking fails
    var abs = ctx.reify(t2)
    for (g <- os) {
      abs = Abstract.Lambda(Abstract.Closure(Seq.empty, abs))
      typ = typ.whnf match {
        case f: Value.Function => f.codomain(g)
        case _ => logicError()
      }
    }
    // FIXME type checking??
    debug(s"meta solved with $abs", 1)
    val v = ctx.eval(abs)
    m.state = Value.MetaState.Closed(v)
    typ
  }

}
