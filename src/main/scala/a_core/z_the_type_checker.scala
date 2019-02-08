package a_core




class TypeChecker extends Evaluator with ContextManager {

  protected def infer(term: Term): Value = {
    term match {
      case LocalReference(index) => localReferenceType(index)
      case Lambda(domain, body) =>
      case Pi(domain, body) =>
      case Application(left, right) =>
      case RecordField(name, body) =>
      case Record(fields) =>
      case MakeField(name, body) =>
      case Make(makes) =>
      case Projection(left, right) =>
      case Globally => throw new Exception("You should not call Globally other than Projection(Self, _)")
      case Sum(branches) =>
      case Construct(name, data) =>
      case Split(left, right) =>
    }
  }

  protected def check(term: Term, typ: Value): Unit = {
    term match {
      case LocalReference(index) =>
      case Lambda(domain, body) =>
      case Pi(domain, body) =>
      case Application(left, right) =>
      case RecordField(name, body) =>
      case Record(fields) =>
      case MakeField(name, body) =>
      case Make(makes) =>
      case Projection(left, right) =>
      case Globally => throw new Exception("You should not call Globally other than Projection(Self, _)")
      case Sum(branches) =>
      case Construct(name, data) =>
      case Split(left, right) =>
    }
  }


  def check(module: Make): Value = infer(module)
}
