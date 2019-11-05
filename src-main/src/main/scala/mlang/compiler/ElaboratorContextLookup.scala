package mlang.compiler


import mlang.utils._
import mlang.compiler.semantic.Value
import mlang.compiler.`abstract`.Abstract

import scala.collection.mutable

sealed trait ElaboratorContextLookupException extends CompilerException

object ElaboratorContextLookupException {
  case class NonExistingReference(name: Text) extends Exception(s"Non existing reference $name") with ElaboratorContextLookupException
  case class ReferenceSortWrong(name: Text) extends Exception(s"Reference sort wrong $name") with ElaboratorContextLookupException
}

sealed trait NameLookupResult
object NameLookupResult {
  sealed trait Term extends NameLookupResult
  case class Typed(typ: Value, ref: Abstract) extends Term
  case class Construct(self: Value, index: Int, closure: semantic.ClosureGraph) extends Term
  case class Dimension(ref: `abstract`.Formula) extends NameLookupResult
}

trait ElaboratorContextLookup extends ElaboratorContextBase {

  def lookupTerm(name: Text): NameLookupResult.Term = {
    lookup0(name) match {
      case t: NameLookupResult.Term => t
      case _ => throw ElaboratorContextLookupException.ReferenceSortWrong(name)
    }
  }


  def lookupDimension(name: Text): NameLookupResult.Dimension = {
    lookup0(name) match {
      case name: NameLookupResult.Dimension => name
      case _ => throw ElaboratorContextLookupException.ReferenceSortWrong(name)
    }
  }

  private def lookup0(name: Text): NameLookupResult =  {
    var up = 0
    var ls = layers
    var binder: NameLookupResult = null
    def mkTyped(gn: Value.Generic, abs: Abstract.Reference): NameLookupResult.Typed = {
      // we use generic here because it is cached
      NameLookupResult.Typed(getRestricted(gn, up).asInstanceOf[Value.Generic].typ, abs)
    }
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case ly: Layer.Parameters =>
          var ll = ly.binders
          var index = -1
          while (ll.nonEmpty && binder == null) {
            val hd = ll.head
            if (hd.name.by(name)) {
              index = i
              hd match {
                case p: ParameterBinder =>
                  binder = mkTyped(p.value, Abstract.Reference(up, ly.typedIndex(index)))
                case d: DimensionBinder =>
                  binder = NameLookupResult.Dimension(`abstract`.Formula.Reference(up, ly.typedIndex(index)))
              }
            }
            i += 1
            ll = ll.tail
          }
          if (binder == null) {
            ly match {
              case l: Layer.ParameterGraph =>
                l.hit.foreach(hit => {
                  hit.branches.zipWithIndex.find(_._1.name.by(name)).foreach(f => {
                    binder = NameLookupResult.Construct(hit.self, f._2, f._1.ps)
                  })
                })
              case _ =>
            }
          }
        case ly: Layer.Defines =>
          var ll = ly.terms
          var index = -1
          while (ll.nonEmpty && binder == null) {
            if (ll.head.name.by(name)) {
              index = i
              binder = mkTyped(ll.head.typ0.value,
                  Abstract.Reference(up, index))
            }
            i += 1
            ll = ll.tail
          }
        case p:Layer.Parameter =>
          if (p.binder.name.by(name)) {
            binder = mkTyped(p.binder.value, Abstract.Reference(up, -1))
          }
        case d: Layer.Dimension =>
          if (d.binder.name.by(name)) {
            binder = NameLookupResult.Dimension(`abstract`.Formula.Reference(up, -1))
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
      binder
    }
  }
}

