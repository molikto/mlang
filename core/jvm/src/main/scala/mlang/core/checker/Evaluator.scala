package mlang.core.checker

import mlang.core.concrete.Term


trait Evaluator extends ContextBuilder {

  def platformEval(term: Term): Value = {
    ???
  }
}
