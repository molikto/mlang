package mlang.core


import mlang.utils._
import mlang.syntax._

/**
  * context is syntactical. adding a layer always occurs when a new binder is introduced. that's why we can give each
  * layer a unique id upon building the layer. it is like a abstract and simple version of "source position"
  */
// the head is the newest layer, unlike a context in type theory x: A, y: B(x)


case class TypeValue(typ: Value, value: Value)

object ContextLayer {

  case class Declaration(id: Long, typ: Value, value: Option[Value] = None)

}

import ContextLayer._


enum ContextLayer {
  // used for pi and lambda and prameters for inductive type/arguments
  case Abstraction (id: Long, name: Unicode, typ: mlang.core.Value)
  // for make, record
  case Declarations (definitions: Map[Unicode, Declaration])
  case Path(id: Long, name: Unicode)
  case Cofibration (restriction: Cofibration)
}

opaque type Context = Seq[ContextLayer]

opaque type IdProvider = Long

object Context {


  def empty: Context = Seq.empty

  object LookupMethods {

    def lookupValue(n: Unicode) given (c: Context): Option[TypeValue] = c.firstOption {
      case Abstraction(id, name, typ) => if (name == n) Some(TypeValue(typ, ???)) else None
      case Declarations(ds) => ds.get(n).map(d => TypeValue(d.typ, d.value.get))
      case Path(_, name) => if (name == n) throw new Exception("Not a value") else None
      case Cofibration(_) => None
    }
  }

  object Builders {

    def newAbstraction(name: Unicode, typ: Value) given (c: Context): (Context, Value) = {
      val id = newUniqueId()
      val ct = ContextLayer.Abstraction(id, name, typ) +: c
      (ct, Value.OpenReference(id, name))
    }

    def newTypeDeclaration(name: Unicode, typ: Value) given (c: Context): (Context, Value) = c.headOption match {
      case Some(ContextLayer.Declarations(declarations)) => declarations.get(name) match {
        case Some(ty) =>
          if (ty.typ == typ) {
            (c, ty.value.getOrElse(Value.OpenReference(ty.id, name)))
          } else {
            throw new IllegalStateException("Duplicated type declaration")
          }
        case None =>
          val id = newUniqueId()
          val ct = ContextLayer.Declarations(declarations.updated(name, Declaration(id, typ))) +: c.tail
          (ct, Value.OpenReference(id, name))
      }
      case _ => throw new Exception("Wrong layer type or not enough layer")
    }


    /**
      * note that if a type is already declared, a object eq check will be performed, so the intended usage is
      * check if there is a type, check the type, and then pass back that thing back if there is one
      */
    def newDeclaration(name: Unicode, value: Value, typ: Value) given (c: Context): Context = c.headOption match {
      case Some(ContextLayer.Declarations(declarations)) => declarations.get(name) match {
        case Some(dec) => dec.value match {
          case Some(_) =>
            throw new IllegalStateException("Duplicated declaration")
          case None =>
            if (dec.typ == typ) {
              ContextLayer.Declarations(declarations.updated(name, Declaration(dec.id, dec.typ, Some(value)))) +: c.tail
            } else {
              throw new IllegalStateException("Declared type doesn't match")
            }
        }
        case None => ContextLayer.Declarations(declarations.updated(name, Declaration(newUniqueId(), typ, Some(value)))) +: c.tail
      }
      case _ => throw new Exception("Wrong layer type or not enough layer")
    }

    // TODO dotty don't want this to be refer to previous one
    // def newDeclarations(map: Map[Unicode, Value]) given (c: Context): Context =
    //   ContextLayer.Declarations(map.mapValues(t => Declaration(newUniqueId(), t))) +: c

    def newDeclarations() given (c: Context): Context =
      ContextLayer.Declarations(Map.empty) +: c
  }
}

