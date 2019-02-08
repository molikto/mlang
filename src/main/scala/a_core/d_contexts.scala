package a_core

import java.util.concurrent.atomic.AtomicLong

/**
  * suitable for adding more layers, for example path abstractions...
  *
  * context is syntactical. adding a layer always occurs when a new binder is introduced. that's why we can give each
  * layer a unique id upon building the layer. it is like a abstract and simple version of "source position"
  */
// the head is the newest layer, unlike a context in type theory x: A, y: B(x)
trait Context[Value <: AnyRef] {

  sealed trait ContextLayer

  case class LambdaLayer(typ: Value) extends ContextLayer

  case class Declaration(typ: Value, value: Option[Value] = None)

  case class DeclarationLayer(definitions: Map[String, Declaration]) extends ContextLayer

  private val uniqueIdGen =  new AtomicLong(0)

  protected def newUniqueId(): Long = uniqueIdGen.incrementAndGet()

  case class LayerWithId(layer: ContextLayer, id: Long)
  type Layers = Seq[LayerWithId]

  protected def layers: Layers

  def layer(index: Int): Option[ContextLayer] = layers.lift(index).map(_.layer)

  def layerId(index: Int): Option[Long] = layers.lift(index).map(_.id)

  def abstractionType(index: Int): Option[Value] = layer(index).flatMap {
      case LambdaLayer(typ) => Some(typ)
      case _ => None
  }

  def declarationValue(index: Int, name: String): Option[Value] = layer(index).flatMap {
    case DeclarationLayer(ds) => ds.get(name).flatMap(_.value)
    case _ => None
  }

  def declaration(index: Int, name: String): Option[Declaration] = layer(index).flatMap {
    case DeclarationLayer(ds) => ds.get(name)
    case _ => None
  }

  def declarationType(index: Int, name: String): Option[Value] = layer(index).flatMap {
    case DeclarationLayer(ds) => ds.get(name).map(_.typ)
    case _ => None
  }

  def declarationTypes(index: Int): Option[Map[String, Value]] = layer(index).flatMap {
    case DeclarationLayer(ds) => Some(ds.mapValues(_.typ))
    case _ => None
  }
}

trait ContextBuilder[Value <: AnyRef] extends Context[Value] {

  type Self <: ContextBuilder[Value]

  protected def newBuilder(layers: Layers): Self

  protected def newTypeDeclaration(name: String, typ: Value): Self = newBuilder(layers.head.layer match {
    case DeclarationLayer(declarations) => declarations.get(name) match {
      case Some(_) =>
        throw new Exception("Duplicated declaration")
      case None =>
        LayerWithId(DeclarationLayer(declarations.updated(name, Declaration(typ))), layers.head.id) +: layers.tail
    }
    case _ => throw new Exception("Wrong layer type")
  })


  protected def replaceDeclarationValue(name: String, value: Value): Self =  newBuilder(layers.head.layer match {
    case DeclarationLayer(declarations) => declarations.get(name) match {
      case Some(dec) => dec.value match {
        case Some(_) =>
          LayerWithId(DeclarationLayer(declarations.updated(name, Declaration(dec.typ, Some(value)))), layers.head.id) +: layers.tail
        case None =>
          throw new Exception(s"Replace should only be called on values already has a value")
      }
      case None =>
        throw new Exception(s"Cannot find declaration $name")
    }
    case _ => throw new Exception("Wrong layer type")
  })
  /**
    * note that if a type is already declared, a object eq check will be performed, so the intended usage is
    * check if there is a type, check the type, and then pass back that thing back if there is one
    */
  protected def newDeclaration(name: String, value: Value, typ: Value): Self = newBuilder(layers.head.layer match {
    case DeclarationLayer(declarations) => declarations.get(name) match {
      case Some(dec) => dec.value match {
        case Some(_) =>
          throw new Exception("Duplicated declaration")
        case None =>
          assert(dec.typ.eq(typ), "Declared value doesn't match")
          LayerWithId(DeclarationLayer(declarations.updated(name, Declaration(dec.typ, Some(value)))), layers.head.id) +: layers.tail
      }
      case None => LayerWithId(DeclarationLayer(declarations.updated(name, Declaration(typ, Some(value)))), layers.head.id) +: layers.tail
    }
    case _ => throw new Exception("Wrong layer type")
  })

  protected def newDeclarationLayer(map: Map[String, Value]): Self =
    newBuilder(LayerWithId(DeclarationLayer(map.mapValues(t => Declaration(t))), newUniqueId()) +: layers)

  protected def newDeclarationLayer(): Self = newDeclarationLayer(Map.empty)

  protected def newAbstractionLayer(typ: Value): Self = newBuilder(LayerWithId(LambdaLayer(typ), newUniqueId()) +: layers)
}
