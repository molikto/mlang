package mlang.core

// a evaluator using dbj index shifting
trait DirectEvaluator extends BaseEvaluator {

  override protected def platformEval(value: Abstract): Value = {
    ???
  }

  override protected def platformEvalRecursive(terms: Map[Int, Abstract]): Map[Int, Value] = {
    ???
  }
}
