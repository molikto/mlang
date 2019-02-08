package a_core

import java.util.concurrent.atomic.AtomicLong

/**
  * suitable for adding more layers, for example path abstractions...
  */





// the head is the newest layer, unlike a context in type theory x: A, y: B(x)
trait Context[Value <: AnyRef] {

  abstract sealed trait ContextLayer

  case class LambdaLayer(typ: Value) extends ContextLayer

  case class Declaration(typ: Value, value: Option[Value] = None)

  case class DeclarationLayer(definitions: Map[String, Declaration]) extends ContextLayer

  private val uniqueIdGen =  new AtomicLong(0)

  def newUniqueId() = uniqueIdGen.incrementAndGet()

  type Layers = Seq[(ContextLayer, Long)]

  protected def layers: Layers

  def layer(index: Int): Option[ContextLayer] = layers.lift(index).map(_._1)

  def layerId(index: Int): Option[Long] = layers.lift(index).map(_._2)

  def abstractionType(index: Int): Option[Value] = layer(index).flatMap {
      case LambdaLayer(typ) => Some(typ)
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

  def newTypeDeclaration(name: String, typ: Value): Self = newBuilder(layers.head._1 match {
    case DeclarationLayer(declarations) => declarations.get(name) match {
      case Some(_) =>
        throw new Exception("Duplicated declaration")
      case None =>
        (DeclarationLayer(declarations.updated(name, Declaration(typ))), layers.head._2) +: layers.tail
    }
    case _ => throw new Exception("Wrong layer type")
  })

  /**
    * note that if a type is already declared, a object eq check will be performed, so the intended usage is
    * check if there is a type, check the type, and then pass back that thing back if there is one
    */
  def newDeclaration(name: String, value: Value, typ: Value): Self = newBuilder(layers.head._1 match {
    case DeclarationLayer(declarations) => declarations.get(name) match {
      case Some(dec) => dec.value match {
        case Some(_) =>
          throw new Exception("Duplicated declaration")
        case None =>
          assert(dec.typ.eq(typ), "Declared value doesn't match")
          (DeclarationLayer(declarations.updated(name, Declaration(dec.typ, Some(value)))), layers.head._2) +: layers.tail
      }
      case None => (DeclarationLayer(declarations.updated(name, Declaration(typ, Some(value)))), layers.head._2) +: layers.tail
    }
    case _ => throw new Exception("Wrong layer type")
  })

  def newDeclarationLayer(map: Map[String, Value]): Self =
    newBuilder((DeclarationLayer(map.mapValues(t => Declaration(t))), newUniqueId()) +: layers)

  def newDeclarationLayer(): Self = newDeclarationLayer(Map.empty)

  def newAbstractionLayer(typ: Value): Self = newBuilder((LambdaLayer(typ), newUniqueId()) +: layers)
}
