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

case class Binder(id: Generic, name: Name, typ: Value, isDefined: Boolean, isAbstraction: Boolean, value: Value)

object Context {
  type Layers = Seq[Layer]
}

sealed trait Layer

object Layer {
  case class Term(binder: Binder) extends Layer
  case class Terms(terms: Seq[Binder]) extends Layer
  case class Dimension(id: Generic, name: Name, value: Value.Dimension) extends Layer
  case class Restriction(res: Value.DimensionPair) extends Layer
}


import Context._
trait Context {

  protected val layers: Layers

  // get value directly without resolving restrictions
  def getTerm(depth: Int, index: Int): Binder =
    if (index == -1) layers(depth).asInstanceOf[Layer.Term].binder
    else layers(depth).asInstanceOf[Layer.Terms].terms(index)

  def getDimension(depth: Int): Value.Dimension = layers(depth).asInstanceOf[Layer.Dimension].value

  def rebindReference(v: Reference): Option[Abstract.TermReference] = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.TermReference= null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case Layer.Terms(ll0) =>
          var ll = ll0
          while (ll.nonEmpty && binder == null) {
            if (ll.head.value.eq(v.value)) {
              index = i
              binder = Abstract.TermReference(up, index, v.closed)
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
      case Value.Dimension.OpenReference(stuck) =>
        rebindDimensionOpenReference(stuck)
      case Value.Dimension.Constant(isOne) => Abstract.Dimension.Constant(isOne)
    }
  }

  def rebindDimensionOpenReference(id: Generic): Abstract.Dimension.Reference = {
    var up = 0
    var ls = layers
    var binder: Abstract.Dimension.Reference = null
    while (ls.nonEmpty && binder == null) {
      ls.head match {
        case Layer.Dimension(idd, _, _) =>
          if (idd == id) {
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

  def rebindOpenReference(id: Generic): Abstract.TermReference = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.TermReference = null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case Layer.Terms(ll0) =>
          var ll = ll0
          while (ll.nonEmpty && binder == null) {
            if (ll.head.id == id) {
              index = i
              binder = Abstract.TermReference(up, index)
            }
            i += 1
            ll = ll.tail
          }
        case Layer.Term(l) =>
          if (l.id == id) {
            index = i
            binder = Abstract.TermReference(up, -1)
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
    val restrictions = mutable.ArrayBuffer[Layer.Restriction]()
    val dimensionsUnder = mutable.ArrayBuffer[Generic]()
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case Layer.Terms(ll0) =>
          var ll = ll0
          var index = -1
          while (ll.nonEmpty && binder == null) {
            if (ll.head.name.by(name)) {
              index = i
              binder = (ll.head.typ, Abstract.TermReference(up, index), ll.head.isAbstraction)
            }
            i += 1
            ll = ll.tail
          }
        case Layer.Term(b) =>
          if (b.name.by(name)) {
            binder = (b.typ, Abstract.TermReference(up, -1), true)
          }
        case d@Layer.Dimension(_, n, _) =>
          if (n.by(name)) {
            binder = (d.value, Abstract.Dimension.Reference(up), true)
          } else {
            dimensionsUnder.append(d.id)
          }
        case l@Layer.Restriction(_) =>
          restrictions.append(l)
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    if (binder == null) {
      throw ContextException.NonExistingReference(name)
    } else {
      def contains(a: Value.Dimension) = {
        a match {
          case Dimension.OpenReference(id) => dimensionsUnder.contains(id)
          case _ => true // can only be constants, restrictions is normalized
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
            (recv(t, restrictions), reca(j, restrictions))
          } else {
            // in case of definitions, don't restrict any thing defined after it. they don't have a clue what it is
            val rs = restrictions.filter(r => !contains(r.res.from) || !contains(r.res.to))
            (recv(t, rs), reca(j, rs))
          }
        case (t: Value.Dimension, j: Abstract.Dimension, _: Boolean) =>
          (recvd(t, restrictions), recad(j, restrictions))
        case _ => logicError()
      }
    }
  }
}