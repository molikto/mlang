package mlang.compiler

import mlang.utils.Text


sealed trait ElaborationContextException extends CompilerException

object ElaborationContextException {
  case class NonExistingReference(name: Text) extends Exception(s"Non existing reference $name") with ElaborationContextException
  case class ReferenceSortWrong(name: Text) extends ElaborationContextException
  case class ConstantSortWrong() extends ElaborationContextException
}


