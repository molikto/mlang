package mlang.compiler


import mlang.utils._
import mlang.compiler.semantic.Value
import mlang.compiler.dbi.Abstract

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
  case class Construct(self: Value, index: Int, ims: Seq[Boolean], closure: semantic.ClosureGraph) extends Term
  case class Dimension(ref: dbi.Formula) extends NameLookupResult
}

trait ElaboratorContextLookup extends ElaboratorContextBase {

  def lookupTerm(name: Text, lvl: Int): NameLookupResult.Term = {
    lookup0(name, lvl) match {
      case t: NameLookupResult.Term => t
      case _ => throw ElaboratorContextLookupException.ReferenceSortWrong(name)
    }
  }


  def lookupDimension(name: Text): NameLookupResult.Dimension = {
    lookup0(name, 0) match {
      case name: NameLookupResult.Dimension => name
      case _ => throw ElaboratorContextLookupException.ReferenceSortWrong(name)
    }
  }

  private def lookup0(name: Text, lvl: Int): NameLookupResult =  {
    var up = 0
    var ls = layers
    var binder: NameLookupResult = null
    def mkTyped(gn: Value.Referential, abs: Abstract.Reference): NameLookupResult.Typed = {
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
                  binder = mkTyped(p.value.get(evalHack, lvl), Abstract.Reference(up, ly.typedIndex(index), 0))
                case d: DimensionBinder =>
                  binder = NameLookupResult.Dimension(dbi.Formula.Reference(up, ly.typedIndex(index)))
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
                    binder = NameLookupResult.Construct(hit.self, f._2, f._1.ims, f._1.ps)
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
              binder = mkTyped(ll.head.typ0.value.get(evalHack, lvl),
                  Abstract.Reference(up, index, lvl))
            }
            i += 1
            ll = ll.tail
          }
        case p:Layer.Parameter =>
          if (p.binder.name.by(name)) {
            binder = mkTyped(p.binder.value.get(evalHack, lvl), Abstract.Reference(up, -1, 0))
          }
        case d: Layer.Dimension =>
          if (d.binder.name.by(name)) {
            binder = NameLookupResult.Dimension(dbi.Formula.Reference(up, -1))
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

