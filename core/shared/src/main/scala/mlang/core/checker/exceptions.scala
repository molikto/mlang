package mlang.core.checker

import mlang.core.concrete.Name


trait CoreException extends Exception


sealed trait ContextException extends Exception

object ContextException {

  // resolve
  class NonExistingReference(name: Name) extends ContextException

  // build
  class AlreadyDeclared() extends ContextException
  class AlreadyDefined() extends ContextException
  class NotDeclared() extends ContextException

}