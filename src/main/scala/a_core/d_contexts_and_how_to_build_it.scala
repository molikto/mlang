package a_core


/**
  * suitable for adding more layers, for example path abstractions...
  */
abstract sealed trait ContextLayer

object Context {

  case class LambdaLayer(typ: Value) extends ContextLayer

  case class Declaration(typ: Value, value: Option[Value] = None)

  case class DeclarationLayer(definitions: Map[String, Declaration]) extends ContextLayer
}

import Context._


// the head is the newest layer, unlike a context in type theory x: A, y: B(x)
trait Context {
  protected val layers: Seq[ContextLayer] = Seq.empty

  def abstractionType(index: Int): Option[Value] = {
    val values = (layers.flatMap {
      case LambdaLayer(typ) => Some(typ)
      case _ => None
    })
    values.lift(index)
  }

  def declarationType(index: Int, name: String): Option[Value] = {
    val values = (layers.flatMap {
      case DeclarationLayer(typ) => Some(typ)
      case _ => None
    })
    values.lift(index).flatMap(_.get(name).map(_.typ))
  }

  def declarationTypes(index: Int): Map[String, Value] = {
    val values = (layers.flatMap {
      case DeclarationLayer(typ) => Some(typ)
      case _ => None
    })
    values.lift(index).map(_.mapValues(_.typ))
  }
}

trait ContextBuilder extends Context {

  type Self <: ContextBuilder
  protected def newBuilder(layers: Seq[ContextLayer]): Self

  def newTypeDeclaration(name: String, typ: Value): Self = newBuilder(layers.head match {
    case DeclarationLayer(declarations) => declarations.get(name) match {
      case Some(_) =>
        throw new Exception("Duplicated declaration")
      case None =>
        DeclarationLayer(declarations.updated(name, Declaration(typ))) +: layers.tail
    }
  })

  def newDeclaration(name: String, value: Value, typ: Value): Self = newBuilder(layers.head match {
    case DeclarationLayer(declarations) => declarations.get(name) match {
      case Some(dec) => dec.value match {
        case Some(_) =>
          throw new Exception("Duplicated declaration")
        case None =>
          assert(dec.typ == typ, "Declared value doesn't match")
          DeclarationLayer(declarations.updated(name, Declaration(dec.typ, Some(value)))) +: layers.tail
      }
      case None => DeclarationLayer(declarations.updated(name, Declaration(typ, Some(value)))) +: layers.tail
    }
  })

  def newDeclarationLayer(map: Map[String, Value]): Self = newBuilder(DeclarationLayer(map.mapValues(t => Declaration(t))) +: layers)

  def newDeclarationLayer(): Self = newDeclarationLayer(Map.empty)

  def newAbstractionLayer(typ: Value): Self = newBuilder(LambdaLayer(typ) +: layers)

}
