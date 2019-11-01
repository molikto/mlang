package mlang.compiler

import mlang.compiler.Abstract.Formula
import mlang.utils.{Benchmark, Name, debug}

import scala.collection.mutable

case class PlatformEvaluatorException(src: String, cause: Throwable)
    extends Exception(s"Src: $src", cause) with CompilerException


trait Evaluator extends EvaluatorContext {



  protected def platformEval(value: Abstract): Value

  protected def eval(a: Abstract.AbsClosure): Value.AbsClosure = {
    eval(Abstract.PathLambda(a)).asInstanceOf[Value.PathLambda].body
  }

  protected def eval(a: Abstract.ClosureGraph): Value.ClosureGraph = {
    // TOOD this is ugly
    if (a.nodes.isEmpty && a.dims == 0) {
      Value.ClosureGraph.empty
    } else {
      eval(Abstract.Record(None, a.nodes.map(_ => Name.empty), a)).asInstanceOf[Value.Record].nodes
    }
  }

  protected def eval(a: Abstract.Formula): Value.Formula = {
    a match {
      case Formula.Reference(up, index) => getDimension(up, index)
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
