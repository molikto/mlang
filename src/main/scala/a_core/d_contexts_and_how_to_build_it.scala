package a_core


/**
  * suitable for adding more layers, for example path abstractions...
  */
abstract sealed trait ContextLayer

case class LambdaLayer(typ: Value) extends ContextLayer

case class Definition(name: String, typ: Value, value: Option[Value])

case class DefinitionLayer(definitions: Seq[Definition]) extends ContextLayer


trait Contextual {

  // the head is the newest layer, unlike a context in type theory x: A, y: B(x)
  private val contextLayers: Seq[ContextLayer] = Seq.empty

  protected def localReferenceType(index: Int): Value = {
    val values = (contextLayers.flatMap {
      case LambdaLayer(typ) => Some(typ)
      case _ => None
    })
    values(index)
  }
}


trait ContextManager extends Contextual {

}