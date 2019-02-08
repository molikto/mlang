package a_core



trait Evaluator extends Contextual {


  /**
    *
    * we evaluate will typed terms by NBE,
    * @param context
    * @param term a term that is **valid** under the parameter context
    * @return
    */
  protected def eval(term: Term): Value = ???


  protected def equal(a: Value, b: Value) = ???
}

