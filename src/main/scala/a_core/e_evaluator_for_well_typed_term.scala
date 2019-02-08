package a_core

import com.twitter.util.Eval


trait Evaluator extends Context[Value] {

  /**
    *
    * we evaluate will **valid typechecked terms** by NBE
    */
  private def emit(term: Term, depth: Int): String = {
    ??? // TODO
//    term match {
//      case VariableReference(index) =>
//        if (index > depth) s"OpenAbstractionReference(${abstractionType()})"
//      case Lambda(domain, body) =>
//      case Pi(domain, body) =>
//      case Application(left, right) =>
//      case Record(fields) =>
//      case Make(declarations) =>
//      case Projection(left, name) =>
//      case DeclarationReference(index, name) =>
//      case Sum(branches) =>
//      case Construct(name, data) =>
//      case Split(left, right) =>
//    }
  }

  protected def eval(term: Term): Value = {
    val source = emit(term, -1)
    val twitterEval = new Eval()
    twitterEval.apply[Value](source)
  }

  protected def equal(a: Value, b: Value): Boolean = {
    if (a.eq(b)) {
      true
    } else {
      ??? // TODO
    }
  }

  protected def nonEmptyJoin(vs: Seq[Value]): Value = {
    assert(vs.tail.forall(a => equal(a, vs.head)), "The join is invalid, we currently only joins equal types")
    vs.head
  }
}

