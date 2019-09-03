package mlang.compiler


import mlang.utils._

import scala.collection.mutable

sealed trait ElaborationContextLookupException extends CompilerException

object ElaborationContextLookupException {
  case class NonExistingReference(name: Text) extends Exception(s"Non existing reference $name") with ElaborationContextLookupException
  case class ReferenceSortWrong(name: Text) extends ElaborationContextLookupException
}

trait ElaboratorContextLookup extends ElaboratorContextBase with ElaboratorContextRebind {

  def lookupTerm(name: Text): (Value, Abstract) = {
    lookup0(name) match {
      case (t: Value, j: Abstract) =>
        (t, j)
      case _ =>
        throw ElaborationContextLookupException.ReferenceSortWrong(name)
    }
  }

  def lookupDimension(name: Text): (Value.Formula.Generic, Abstract.Formula.Reference) = {
    lookup0(name) match {
      case (t: Value.Formula.Generic, j: Abstract.Formula.Reference) =>
        (t, j)
      case _ =>
        throw ElaborationContextLookupException.ReferenceSortWrong(name)
    }
  }

  private def lookup0(name: Text): (Object, Object) =  {
    var up = 0
    var ls = layers
    var binder: (Object, Object) = null
    val faces = mutable.ArrayBuffer[Layer.Restriction]()
    var isGlobalDefinition = false
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
              isGlobalDefinition = ls.size == 1 // FIXME maybe this should be better
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
            binder = (d.value, Abstract.Formula.Reference(up))
          }
        case l: Layer.Restriction =>
          faces.append(l)
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    val rs = faces.map(_.res).toSeq
    if (binder == null) {
      throw ElaborationContextLookupException.NonExistingReference(name)
    } else {
      binder match {
        case (t: Value, j: Abstract) =>
          if (isGlobalDefinition) {
            (t, j)
          } else {
            (t.restrict(rs), j)
          }
        case (t: Value.Formula.Generic, j: Abstract.Formula.Reference) =>
          (t.restrict(rs), j)
        case _ => logicError()
      }
    }
  }
}

