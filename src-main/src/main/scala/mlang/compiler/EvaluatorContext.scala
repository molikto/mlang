package mlang.compiler

// ideally the key/value of the value context should be defined at here, but now it is not
trait EvaluatorContext {

  def getMetaReference(depth: Int, index: Int): Value

  // get value directly without resolving faces
  def getReference(depth: Int, index: Int): Value

  def getDimension(depth: Int, index: Int): Value.Formula
}