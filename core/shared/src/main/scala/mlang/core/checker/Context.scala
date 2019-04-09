package mlang.core.checker

import mlang.core.concrete.{Name, NameRef, Pattern}




case class Binder(id: Generic, name: Name, typ: Value, value: Option[Value] = None)

object Context {
  type Layer = Seq[Binder]
  type Layers = Seq[Layer]
}

import Context._
trait Context extends GenericGen {

  protected val layers: Layers

  def lookup(name: NameRef): Option[(Binder, Abstract.AbstractReference)] =  {
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
      ls = ls.tail
      up += 1
    }
    if (binder == null) {
      None
    } else {
      Some((binder, Abstract.AbstractReference(up, index, name)))
    }
  }
}


trait ContextBuilder extends Context {

  type Self <: ContextBuilder

  protected implicit def create(a: Layers): Self

}
