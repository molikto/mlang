package mlang.compiler


import mlang.utils._

import scala.collection.mutable

sealed trait ElaboratorContextLookupException extends CompilerException

object ElaboratorContextLookupException {
  case class NonExistingReference(name: Text) extends Exception(s"Non existing reference $name") with ElaboratorContextLookupException
  case class ReferenceSortWrong(name: Text) extends Exception(s"Reference sort wrong $name") with ElaboratorContextLookupException
}

trait ElaboratorContextLookup extends ElaboratorContextBase {

  def lookupTerm(name: Text): (Value, Abstract) = {
    lookup0(name) match {
      case (t: Value, j: Abstract) =>
        (t, j)
      case _ =>
        throw ElaboratorContextLookupException.ReferenceSortWrong(name)
    }
  }


  def lookupDimension(name: Text): Abstract.Formula.Reference = {
    lookup0(name) match {
      case (_: String, j: Abstract.Formula.Reference) =>
        j
      case _ =>
        throw ElaboratorContextLookupException.ReferenceSortWrong(name)
    }
  }

  private def lookup0(name: Text): (Object, Object) = {
    var up = 0
    var ls = layers
    var binder: (Object, Object) = null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case ly: Layer.Parameters =>
          var ll = ly.binders
          var index = -1
          while (ll.nonEmpty && binder == null) {
            if (ll.head.name.by(name)) {
              index = i
              binder = (ll.head.typ,
                  Abstract.Reference(up, index))
            }
            i += 1
            ll = ll.tail
          }
        case ly: Layer.Defines =>
          var ll = ly.terms
          var index = -1
          while (ll.nonEmpty && binder == null) {
            if (ll.head.name.by(name)) {
              index = i
              binder = (ll.head.typ,
                  Abstract.Reference(up, index))
            }
            i += 1
            ll = ll.tail
          }
        case p:Layer.Parameter =>
          if (p.binder.name.by(name)) {
            binder = (p.binder.typ, Abstract.Reference(up, -1))
          }
        case d: Layer.Dimension =>
          if (d.name.by(name)) {
            binder = ("", Abstract.Formula.Reference(up))
          }
        case _ =>
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    if (binder == null) {
      throw ElaboratorContextLookupException.NonExistingReference(name)
    } else {
      binder match {
        case (t: Value, j: Abstract.Reference) =>
          (t.restrict(getAllRestrictions(j.up)), j)
        case (a: String, j: Abstract.Formula.Reference) =>
          (a, j)
        case _ => logicError()
      }
    }
  }
}

