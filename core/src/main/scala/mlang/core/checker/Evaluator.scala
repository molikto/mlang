package mlang.core.checker

import mlang.core.concrete.Term


trait Evaluator extends Context {


  def eval(term: Term): Value = ???
}
