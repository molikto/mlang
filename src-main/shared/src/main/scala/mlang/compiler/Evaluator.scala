package mlang.compiler

import mlang.utils.{Benchmark, debug}

import scala.collection.mutable

case class PlatformEvaluatorException(src: String, cause: Throwable)
    extends Exception(s"Src: $src", cause) with CompilerException

trait Holder {
  def value(c: EvaluationContext, vs: Seq[Any]): Value
}

trait Evaluator extends EvaluationContext {


  private val vs = mutable.ArrayBuffer[Any]()

  protected def extractFromHolder(h: Holder): Value = {
    val res = h.value(this, vs.toSeq)
    if (debug.enabled) {
      for (v <- vs.indices) debug(s"v$v: ${vs(v)}")
    }
    vs.clear()
    res
  }


  protected def tunnel(v: Value.Formula): String = {
    val i = vs.size
    vs += v
    s"vs($i).asInstanceOf[Value.Formula]"
  }

  protected def tunnel(v: Value): String = {
    val i = vs.size
    vs += v
    s"vs($i).asInstanceOf[Value]"
  }

  protected def tunnel(v: Value.Closure): String = {
    val i = vs.size
    vs += v
    s"vs($i).asInstanceOf[Value.Closure]"
  }

  protected def tunnel(v: Pattern): String = {
    val i = vs.size
    vs += v
    s"vs($i).asInstanceOf[Pattern]"
  }

  protected def platformEval(value: Abstract): Value

  protected def eval(a: Abstract.AbsClosure): Value.AbsClosure = {
    eval(Abstract.PathLambda(a)).asInstanceOf[Value.PathLambda].body
  }

  def eval(term: Abstract): Value = {
    Benchmark.Eval {
      term match {
        case Abstract.Reference(up, index) => getReference(up, index)
        case Abstract.MetaReference(up, index) => getMetaReference(up, index)
        case Abstract.Universe(i) => Value.Universe(i)
        case _ =>
          val ret = platformEval(term)
          assert(ret != null)
          ret
      }
    }
  }
}
