package mlang.compiler

import mlang.compiler.Abstract.Formula
import mlang.utils.{Benchmark, debug}

import scala.collection.mutable

case class PlatformEvaluatorException(src: String, cause: Throwable)
    extends Exception(s"Src: $src", cause) with CompilerException

trait Holder {
  def value(c: EvaluatorContext, vs: Seq[Any]): Value
}

trait Evaluator extends EvaluatorContext {


  private val vs = mutable.ArrayBuffer[Any]()

  protected def extractFromHolder(h: Holder): Value = {
    val res = h.value(this, vs.toSeq)
    if (debug.enabled) {
      for (v <- vs.indices) debug(s"v$v: ${vs(v)}")
    }
    vs.clear()
    res
  }


  private def tunnel(v: Any, str: String): String = {
    val i = vs.size
    vs += v
    s"vs($i).asInstanceOf[$str]"
  }

  protected def tunnel(v: Value.Formula): String = {
    tunnel(v, "Formula")
  }

  protected def tunnel(v: Value): String = {
    tunnel(v, "Value")
  }

  protected def tunnel(v: Value.Closure): String = {
    tunnel(v, "Closure")
  }

  protected def tunnel(v: Pattern): String = {
    tunnel(v, "Pattern")
  }

  protected def platformEval(value: Abstract): Value

  protected def eval(a: Abstract.AbsClosure): Value.AbsClosure = {
    eval(Abstract.PathLambda(a)).asInstanceOf[Value.PathLambda].body
  }

  protected def eval(a: Abstract.Formula): Value.Formula = {
    a match {
      case Formula.Reference(up) => getDimension(up)
      case Formula.True => Value.Formula.True
      case Formula.False => Value.Formula.False
      case Formula.And(left, right) => Value.Formula.And(eval(left), eval(right))
      case Formula.Or(left, right) => Value.Formula.Or(eval(left), eval(right))
      case Formula.Neg(unit) => Value.Formula.Neg(eval(unit))
    }
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
