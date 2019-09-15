package mlang

package object compiler {
  def logicError() = mlang.utils.logicError()

  def logicError(additionalInfo: String) = mlang.utils.logicError(additionalInfo)
}
