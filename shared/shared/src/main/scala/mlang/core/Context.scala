package mlang.core


import mlang.core.Value.{Dimension, Reference}
import mlang.name._

import scala.collection.mutable

sealed trait ContextException extends CoreException

object ContextException {
  case class NonExistingReference(name: Ref) extends Exception(s"Non existing reference $name") with ContextException
  case class ReferenceSortWrong(name: Ref) extends ContextException
  case class ConstantSortWrong() extends ContextException
}


case class ParameterBinder(name: Name, value: Value.Generic) {
  def id: Long = value.id
  def typ: Value = value.typ
}

sealed trait Depends[T] {
  def t: T
}


// a defined term acts like a parameter when it doesn't have a body
case class DefineItem(typ0: ParameterBinder, ref0: Option[Value.Reference]) {
  def typ: Value = typ0.value.typ
  def id: Long = typ0.id
  def name: Name = typ0.name
  def isDefined = ref0.isDefined
  def ref = ref0.getOrElse(typ0.value)
}

object Context {
  type Layers = Seq[Layer]

  class Metas(val metas: mutable.ArrayBuffer[Value.Meta], var frozen: Int) {
    def debug_allFrozen: Boolean = metas.size == frozen

    def freeze(): Seq[Value.Meta] = {
      val vs = metas.slice(frozen, metas.size)
      frozen = metas.size
      vs
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

import Context._

sealed trait Layer {
  val metas: Metas
}

object Layer {

  sealed trait Parameters extends Layer {
    def binders: Seq[ParameterBinder]
  }
  case class Parameter(binder: ParameterBinder, metas: Metas) extends Layer // lambda expression

  case class MultiParameters(binders: Seq[ParameterBinder], metas: Metas) extends Parameters

  case class ParameterGraph(defined: Seq[ParameterBinder], metas: Metas) extends Parameters {
    def binders: Seq[ParameterBinder] = defined
  }

  case class Defines(metas: Metas, terms: Seq[DefineItem]) extends Layer // notice the metas is FIRST!!
  case class Dimension(id: Long, name: Name, metas: Metas) extends Layer {
    val value = Value.Dimension.Generic(id)
  }
  case class Restriction(res: Value.DimensionPair, metas: Metas) extends Layer // no meta should be resolved here
}


import Context._
trait Context extends ContextBaseForMeta {

  protected val layers: Layers

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


  def rebindDimensionPair(a: Value.DimensionPair): Abstract.DimensionPair = {
    Abstract.DimensionPair(rebindDimension(a.from), rebindDimension(a.to))
  }
  def rebindDimension(a: Value.Dimension): Abstract.Dimension = {
    a match {
      case Value.Dimension.Generic(stuck) =>
        rebindDimensionGeneric(stuck)
      case Value.Dimension.True => Abstract.Dimension.True
      case Value.Dimension.False => Abstract.Dimension.False
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
      logicError()
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
      logicError()
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
            if (ll.head.id == id) {
              if (ll.head.isDefined) {
                logicError()
              } else {
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

  def lookupTerm(name: Ref): (Value, Abstract) = {
    lookup0(name) match {
      case (t: Value, j: Abstract) =>
        (t, j)
      case _ =>
        throw ContextException.ReferenceSortWrong(name)
    }
  }

  def lookupDimension(name: Ref): (Value.Dimension, Abstract.Dimension) = {
    lookup0(name) match {
      case (t: Value.Dimension, j: Abstract.Dimension) =>
        (t, j)
      case _ =>
        throw ContextException.ReferenceSortWrong(name)
    }
  }

  private def lookup0(name: Ref): (Object, Object) =  {
    var up = 0
    var ls = layers
    var binder: (Object, Object, Boolean) = null
    val faces = mutable.ArrayBuffer[Layer.Restriction]()
    val dimensionsUnder = mutable.ArrayBuffer[Long]()
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
                  Abstract.Reference(up, index),
                  true)
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
                  Abstract.Reference(up, index),
                  false)
            }
            i += 1
            ll = ll.tail
          }
        case p:Layer.Parameter =>
          if (p.binder.name.by(name)) {
            binder = (p.binder.typ, Abstract.Reference(up, -1), true)
          }
        case d: Layer.Dimension =>
          if (d.name.by(name)) {
            binder = (d.value, Abstract.Dimension.Reference(up), true)
          } else {
            dimensionsUnder.append(d.id)
          }
        case l: Layer.Restriction =>
          faces.append(l)
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    if (binder == null) {
      throw ContextException.NonExistingReference(name)
    } else {
      def contains(a: Value.Dimension): Boolean = {
        a match {
          case Dimension.Generic(id) => dimensionsUnder.contains(id)
          case _ => true // can only be constants, faces is normalized
        }
      }
      // TODO fold duplicated ones
      def recvd(a: Value.Dimension, seq: Seq[Layer.Restriction]): Value.Dimension = {
        seq.foldLeft(a) { (a, h) =>
          a.restrict(h.res)
        }
      }
      def recad(a: Abstract.Dimension, seq: Seq[Layer.Restriction]): Abstract.Dimension = {
        seq.foldLeft(a) { (a, h) =>
          Abstract.Dimension.Restricted(a, rebindDimensionPair(h.res))
        }
      }
      def recv(a: Value, seq: Seq[Layer.Restriction]): Value = {
        seq.foldLeft(a) { (a, h) =>
          a.restrict(h.res)
        }
      }
      def reca(a: Abstract, seq: Seq[Layer.Restriction]): Abstract = {
        seq.foldLeft(a) { (a, h) =>
          Abstract.Restricted(a, rebindDimensionPair(h.res))
        }
      }
      binder match {
        case (t: Value, j: Abstract, abs: Boolean) =>
          if (abs) {
            (recv(t, faces), reca(j, faces))
          } else {
            // in case of definitions, don't restrict any thing defined after it. they don't have a clue what it is
            val rs = faces.filter(r => !contains(r.res.from) || !contains(r.res.to))
            (recv(t, rs), reca(j, rs))
          }
        case (t: Value.Dimension, j: Abstract.Dimension, _: Boolean) =>
          (recvd(t, faces), recad(j, faces))
        case _ => logicError()
      }
    }
  }
}