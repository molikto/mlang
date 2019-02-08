package a_core



trait Evaluator extends Context {

  /**
    *
    * we evaluate will typed terms by NBE,
    * @param context
    * @param term a term that is **valid** under the parameter context
    * @return
    */
  protected def eval(term: Term): Value

  protected def equal(a: Value, b: Value): Boolean

  protected def joinNonEmpty(vs: Seq[Value]): Value = {
    assert(vs.tail.forall(a => equal(a, vs.head)), "The join is invalid, we currently only joins equal types")
    vs.head
  }
}

