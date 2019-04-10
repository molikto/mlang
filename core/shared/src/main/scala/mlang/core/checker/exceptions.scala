package mlang.core.checker



trait CoreException extends Exception


sealed trait ContextException extends Exception

object ContextException {

  // resolve
  class NonExistingReference() extends ContextException

  // build
  class AlreadyDeclared() extends ContextException
  class AlreadyDefined() extends ContextException
  class NotDeclared() extends ContextException

}