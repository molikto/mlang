package a_core

import com.twitter.util.Eval


trait Evaluator extends Context[Value] {

  /**
    *
    * we evaluate will **valid typechecked terms** by NBE
    */
  private def emit(term: Term, depth: Int): String = {
    term match {
      case VariableReference(index) =>
        if (index > depth) s"OpenAbstractionReference(${layerId(index - depth - 1)})"
        else s"r${depth - index}"
      case Lambda(domain, body) =>
        s"LambdaValue(${emit(domain, depth)}, r${depth + 1} => ${emit(body, depth + 1)})"
      case Pi(domain, body) =>
        s"PiValue(${emit(domain, depth)}, r${depth + 1} => ${emit(body, depth + 1)})"
      case Application(left, right) =>
        s"${emit(left, depth)}.application(${emit(right, depth)})"
      case Record(fields) =>
        
      case Make(declarations) =>
      case Projection(left, name) =>
      case DeclarationReference(index, name) =>
        if (index > depth) s"OpenAbstractionReference(${layerId(index - depth - 1)})"
        else s"r${depth - index}"
      case Sum(branches) =>
      case Construct(name, data) =>
      case Split(left, right) =>
    }
  }

  protected def eval(term: Term): Value = {
    val source = "import a_core._" +  emit(term, -1)
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

