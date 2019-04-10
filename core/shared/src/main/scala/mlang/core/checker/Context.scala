package mlang.core.checker


import mlang.core.checker
import mlang.core.concrete.{Name, NameRef}

sealed trait ContextException extends CoreException

object ContextException {

  class NonExistingReference(name: Name) extends ContextException

}

case class Binder(id: Generic, name: Name, typ: Value, value: Option[Value] = None)

object Context {
  type Layer = Seq[Binder]
  type Layers = Seq[Layer]
}

import Context._
trait Context {

  protected val layers: Layers

  def get(depth: Int, index: Int): Binder = layers(depth)(index)

  def lookup(name: NameRef): (Binder, Abstract.Reference) =  {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Binder = null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      var ll = ls.head
      while (ll.nonEmpty && binder == null) {
        if (ll.head.name == name) {
          index = i
          binder = ll.head
        }
        i += 1
        ll = ll.tail
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    if (binder == null) {
      throw new checker.ContextException.NonExistingReference(name)
    } else {
      (binder, Abstract.Reference(up, index, name))
    }
  }
}