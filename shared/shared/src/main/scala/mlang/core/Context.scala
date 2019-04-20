package mlang.core


import mlang.name._

sealed trait ContextException extends CoreException

object ContextException {
  case class NonExistingReference(name: Ref) extends ContextException
  case class ReferenceSortWrong(name: Ref) extends ContextException
  case class ConstantSortWrong() extends ContextException
}

case class Binder(id: Generic, name: Name, typ: Value, isDefined: Boolean, value: Value)

object Context {
  type Layers = Seq[Layer]
}

sealed trait Layer

object Layer {
  case class Terms(terms: Seq[Binder]) extends Layer
  case class Dimension(id: Generic, name: Name, value: Value.Dimension) extends Layer
  case class Restriction() extends Layer
}


import Context._
trait Context {

  protected val layers: Layers

  def getTerm(depth: Int, index: Int): Binder = layers(depth).asInstanceOf[Layer.Terms].terms(index)

  def getDimension(depth: Int): Value.Dimension = layers(depth).asInstanceOf[Layer.Dimension].value

  def lookup(name: Ref): (Binder, Abstract.TermReference) = {
    lookup0(name) match {
      case (t: Binder, j: Abstract.TermReference) =>
        (t, j)
      case _ =>
        throw ContextException.ReferenceSortWrong(name)
    }
  }

  def lookupDimension(name: Ref): (Layer.Dimension, Abstract.Dimension.Reference) = {
    lookup0(name) match {
      case (t: Layer.Dimension, j: Abstract.Dimension.Reference) =>
        (t, j)
      case _ =>
        throw ContextException.ReferenceSortWrong(name)
    }
  }

  private def lookup0(name: Ref): (Object, Object) =  {
    var up = 0
    var index = -1
    var ls = layers
    var binder: (Object, Object) = null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case Layer.Terms(ll0) =>
          var ll = ll0
          while (ll.nonEmpty && binder == null) {
            if (ll.head.name.by(name)) {
              index = i
              binder = (ll.head, Abstract.TermReference(up, index))
            }
            i += 1
            ll = ll.tail
          }
        case d@Layer.Dimension(_, n, _) =>
          if (n.by(name)) {
            binder = (d, Abstract.Dimension.Reference(up))
          }
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    if (binder == null) {
      throw ContextException.NonExistingReference(name)
    } else {
      binder
    }
  }
}