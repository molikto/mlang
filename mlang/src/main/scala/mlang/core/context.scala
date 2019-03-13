package mlang.core


import mlang.utils._

/**
  * context is syntactical. adding a layer always occurs when a new binder is introduced. that's why we can give each
  * layer a unique id upon building the layer. it is like a abstract and simple version of "source position"
  */
// the head is the newest layer, unlike a context in type theory x: A, y: B(x)


sealed case class Declaration(typ: Value, value: Option[Value] = None)

enum ContextLayer {
  // used for pi and lambda and prameters for inductive type/arguments
  case Abstraction(typ: Value)
  // for make, record
  case Declarations(definitions: Map[Unicode, Declaration])
  case Path()
  case Cofibration(restriction: Cofibration)
}

opaque type Context =  Seq[(ContextLayer, Long)]

object Context {

  def empty: Context = Seq.empty

  private def (c: Context) apply1(index: Int): Option[ContextLayer] =  c.lift(index).map(_._1)
  
  def (c: Context) apply(index: Int): Option[ContextLayer] =  c.apply1(index)

  def (c: Context) id(index: Int): Option[Long] = c.lift(index).map(_._2)

  def (c: Context) abstractionType(index: Int): Option[Value] = c.apply1(index).flatMap {
      case ContextLayer.Abstraction(typ) => Some(typ)
      case _ => None
  }

  def (c: Context) declarationValue(index: Int, name: Unicode): Option[Value] = c.apply1(index).flatMap {
    case ContextLayer.Declarations(ds) => ds.get(name).flatMap(_.value)
    case _ => None
  }

  def (c: Context) declaration(index: Int, name: Unicode): Option[Declaration] = c.apply1(index).flatMap {
    case ContextLayer.Declarations(ds) => ds.get(name)
    case _ => None
  }

  def (c: Context) declarationType(index: Int, name: Unicode): Option[Value] = c.apply1(index).flatMap {
    case ContextLayer.Declarations(ds) => ds.get(name).map(_.typ)
    case _ => None
  }

  def (c: Context) declarationTypes(index: Int): Option[Map[Unicode, Value]] = c.apply1(index).flatMap {
    case ContextLayer.Declarations(ds) => Some(ds.mapValues(_.typ))
    case _ => None
  }

  def (c: Context) newTypeDeclaration(name: Unicode, typ: Value): Context = c.head._1 match {
    case ContextLayer.Declarations(declarations) => declarations.get(name) match {
      case Some(ty) =>
        if (ty.typ == typ) {
          c
        } else {
          throw new IllegalStateException("Duplicated type declaration")
        }
      case None =>
        (ContextLayer.Declarations(declarations.updated(name, Declaration(typ))), c.head._2) +: c.tail
    }
    case _ => throw new Exception("Wrong layer type")
  }


  /**
    * note that if a type is already declared, a object eq check will be performed, so the intended usage is
    * check if there is a type, check the type, and then pass back that thing back if there is one
    */
  def (c: Context) newDeclaration(name: Unicode, value: Value, typ: Value): Context = c.head._1 match {
    case ContextLayer.Declarations(declarations) => declarations.get(name) match {
      case Some(dec) => dec.value match {
        case Some(_) =>
          throw new IllegalStateException("Duplicated declaration")
        case None =>
          if (dec.typ == typ) {
            (ContextLayer.Declarations(declarations.updated(name, Declaration(dec.typ, Some(value)))), c.head._2) +: c.tail
          } else {
            throw new IllegalStateException("Declared type doesn't match")
          }
      }
      case None => (ContextLayer.Declarations(declarations.updated(name, Declaration(typ, Some(value)))), c.head._2) +: c.tail
    }
    case _ => throw new Exception("Wrong layer type")
  }

  def (c: Context) newDeclarations(map: Map[Unicode, Value]): Context =
    (ContextLayer.Declarations(map.mapValues(t => Declaration(t))), newUniqueId()) +: c

  // TODO dotty don't want this to be refer to previous one
  def (c: Context) newDeclarations(): Context = 
    (ContextLayer.Declarations(Map.empty), newUniqueId()) +: c

  def (c: Context) newAbstraction(typ: Value): Context = (ContextLayer.Abstraction(typ), newUniqueId()) +: c
}

