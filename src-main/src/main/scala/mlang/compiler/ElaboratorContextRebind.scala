package mlang.compiler

import mlang.compiler.semantic.Value
import mlang.utils._
import mlang.compiler.dbi.Abstract


case class RebindNotFoundException() extends Exception

trait ElaboratorContextRebind extends ElaboratorContextBase {

  def rebindReference(v: Value.Reference): Option[Abstract.Reference] = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.Reference= null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case d: Layer.Defines =>
          var ll = d.terms
          while (ll.nonEmpty && binder == null) {
            ll.head.ref0.flatMap(a => lookupMatched(a, v, up)) match {
              case Some(asgs) =>
                index = i
                binder = Abstract.Reference(up, index)
              case _ =>
            }
            i += 1
            ll = ll.tail
          }
        case _ =>
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    Option(binder)
  }


  def rebindFormula(a: semantic.Formula): dbi.Formula = {
    a match {
      case semantic.Formula.Generic(stuck) =>
        rebindDimension(stuck)
      case semantic.Formula.True => dbi.Formula.True
      case semantic.Formula.False => dbi.Formula.False
      case semantic.Formula.And(a, b) => dbi.Formula.And(rebindFormula(a), rebindFormula(b))
      case semantic.Formula.Or(a, b) => dbi.Formula.Or(rebindFormula(a), rebindFormula(b))
      case semantic.Formula.Neg(a) => dbi.Formula.Neg(rebindFormula(a))
    }
  }


  def rebindDimension(id: Long): dbi.Formula.Reference = {
    var up = 0
    var ls = layers
    var binder: dbi.Formula.Reference = null
    while (ls.nonEmpty && binder == null) {
      ls.head match {
        case d: Layer.Dimension =>
          if (d.id == id) {
            binder = dbi.Formula.Reference(up, -1)
          }
        case d: Layer.Parameters =>
          d.dimensionBinders.zipWithIndex.find(_._1.value.id == id) match {
            case Some(d) => binder = dbi.Formula.Reference(up, d._2)
            case _ =>
          }
        case _ =>
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    if (binder == null) {
      throw RebindNotFoundException()
    } else {
      binder
    }
  }

  def containsGeneric(o: Value.Generic): Boolean = {
    rebindGeneric0(o) != null
  }

  def containsGeneric(o: semantic.Formula.Generic): Boolean = {
    rebindDimension(o.id) != null
  }

  def rebindGeneric(g: Value.Generic): Abstract.Reference = {
    val binder = rebindGeneric0(g)
    if (binder == null) {
      throw RebindNotFoundException()
    } else {
      binder
    }
  }

  private def rebindGeneric0(g: Value.Generic): Abstract.Reference = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.Reference = null
    def tryBind(a: Value.Generic, up: Int, i: Int): Unit = {
      if (g.id == a.id) {
        lookupMatched(a, g, up) match {
          case Some(asgs) =>
            index = i
            binder = Abstract.Reference(up, index)
          case _ => logicError() // you should always bind a generic if id is equal
        }
      }
    }
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case t: Layer.Parameters =>
          var ll = t.termBinders
          while (ll.nonEmpty && binder == null) {
            tryBind(ll.head.value, up, i)
            i += 1
            ll = ll.tail
          }
        case t: Layer.Defines =>
          var ll = t.terms
          while (ll.nonEmpty && binder == null) {
            if (ll.head.isDefined) {
              if (ll.head.id == g.id) logicError()
            } else {
              tryBind(ll.head.typ0.value, up, i)
            }
            i += 1
            ll = ll.tail
          }
        case p:Layer.Parameter =>
          tryBind(p.binder.value, up, -1)
        case _ =>
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    binder
  }

}
