package mlang.compiler


import mlang.compiler.ElaborationContext.Metas
import mlang.compiler.Value.{Dimension, Reference}
import mlang.utils.{Name, Text}

import scala.collection.mutable

case class RebindNotFoundException() extends Exception


object ElaborationContext {
  type Layers = Seq[Layer]

  class Metas(val metas: mutable.ArrayBuffer[Value.Meta], var frozen: Int) {
    def debug_allFrozen: Boolean = metas.size == frozen

    def freeze(): Seq[Value.Meta] = {
      val vs = metas.slice(frozen, metas.size)
      frozen = metas.size
      vs.toSeq
    }

    def apply(i: Int): Value.Meta = metas(i)

    var debug_final = false
    def size: Int = metas.size

    def isEmpty: Boolean = metas.isEmpty
    def nonEmpty: Boolean = metas.nonEmpty
    def head: Value.Meta = metas.head

    def append(a: Value.Meta): Unit = {
      if (debug_final) logicError()
      metas.append(a)
    }
  }
}

import ElaborationContext._



import ElaborationContext._
trait ElaborationContext extends EvaluationContext {

  protected def layers: Layers

  def getMetaReference(depth: Int, index: Int): Value.Meta = layers(depth).metas(index)

  // get value directly without resolving faces
  def getReference(depth: Int, index: Int): Value = layers(depth) match {
    case Layer.Parameter(binder, _) if index == -1 => binder.value
    case ps: Layer.Parameters  => ps.binders(index).value
    case Layer.Defines(_, terms) => terms(index).ref
    case _ => logicError()
  }

  def getDimension(depth: Int): Value.Dimension = layers(depth).asInstanceOf[Layer.Dimension].value

  def rebindReference(v: Reference): Option[Abstract.Reference] = {
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
            if (ll.head.isDefined && ll.head.ref0.get.value.eq(v.value)) {
              index = i
              binder = Abstract.Reference(up, index)
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


  def rebindDimension(a: Value.Dimension): Abstract.Dimension = {
    a match {
      case Value.Dimension.Generic(stuck) =>
        rebindDimensionGeneric(stuck)
      case Value.Dimension.True => Abstract.Dimension.True
      case Value.Dimension.False => Abstract.Dimension.False
      case _: Value.Dimension.Internal => logicError()
    }
  }

  def rebindDimensionGeneric(id: Long): Abstract.Dimension.Reference = {
    var up = 0
    var ls = layers
    var binder: Abstract.Dimension.Reference = null
    while (ls.nonEmpty && binder == null) {
      ls.head match {
        case d: Layer.Dimension =>
          if (d.id == id) {
            binder = Abstract.Dimension.Reference(up)
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

  def containsGeneric(id: Long): Boolean = {
    rebindGeneric0(id) != null
  }

  def rebindGeneric(id: Long): Abstract.Reference = {
    val binder = rebindGeneric0(id)
    if (binder == null) {
      throw RebindNotFoundException()
    } else {
      binder
    }
  }

  private def rebindGeneric0(id: Long): Abstract.Reference = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.Reference = null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case t: Layer.Parameters =>
          var ll = t.binders
          while (ll.nonEmpty && binder == null) {
            if (ll.head.id == id) {
              index = i
              binder = Abstract.Reference(up, index)
            }
            i += 1
            ll = ll.tail
          }
        case t: Layer.Defines =>
          var ll = t.terms
          while (ll.nonEmpty && binder == null) {
            if (!ll.head.isDefined) {
              if (ll.head.id == id) {
                index = i
                binder = Abstract.Reference(up, index)
              }
            }
            i += 1
            ll = ll.tail
          }
        case p:Layer.Parameter =>
          if (p.binder.id == id) {
            index = i
            binder = Abstract.Reference(up, -1)
          }
        case _ =>
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    binder
  }

  def lookupTerm(name: Text): (Value, Abstract) = {
    lookup0(name) match {
      case (t: Value, j: Abstract) =>
        (t, j)
      case _ =>
        throw ElaborationContextException.ReferenceSortWrong(name)
    }
  }

  def lookupDimension(name: Text): (Value.Dimension, Abstract.Dimension) = {
    lookup0(name) match {
      case (t: Value.Dimension, j: Abstract.Dimension) =>
        (t, j)
      case _ =>
        throw ElaborationContextException.ReferenceSortWrong(name)
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
            binder = (d.value, Abstract.Dimension.Reference(up))
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
      throw ElaborationContextException.NonExistingReference(name)
    } else {
      binder match {
        case (t: Value, j: Abstract) =>
          if (isGlobalDefinition) {
            (t, j)
          } else {
            (t.restrict(rs), j)
          }
        case (t: Value.Dimension, j: Abstract.Dimension) =>
          (t.restrict(rs), j)
        case _ => logicError()
      }
    }
  }
}

