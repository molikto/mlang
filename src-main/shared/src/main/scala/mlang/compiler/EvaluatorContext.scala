package mlang.compiler

// ideally the key/value of the value context should be defined at here, but now it is not
trait EvaluatorContext {
  def getDependency(d: Dependency): Option[Value] = if (d.meta) {
    getMetaReference(0, d.i) match {
      case Value.Meta(c: Value.MetaState.Closed) => Some(c.v)
      case _ => None
    }
  } else {
    getReference(0, d.i) match {
      case Value.Reference(v) => Some(v)
      case _: Value.Generic => None
      case _ => logicError()
    }
  }

  def getMetaReference(depth: Int, index: Int): Value.Meta

  // get value directly without resolving faces
  def getReference(depth: Int, index: Int): Value

  def getDimension(depth: Int): Value.Formula.Generic
}