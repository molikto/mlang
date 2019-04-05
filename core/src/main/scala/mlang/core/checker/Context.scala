package mlang.core.checker

import mlang.core.concrete.{Name, NameRef, Pattern}




case class Binder(id: Generic, typ: Value, value: Option[Value] = None)

object Context {
  type Layer = Map[Name, Binder]
  type Layers = Seq[Map[Name, Binder]]
}

import Context._
trait Context extends GenericGen {

  protected val layers: Layers

  def lookup(name: NameRef): Option[Binder] = ???

}


trait ContextBuilder extends Context {

  type Self <: ContextBuilder

  protected implicit def create(a: Layers): Self

}
