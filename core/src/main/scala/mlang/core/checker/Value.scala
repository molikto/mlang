package mlang.core.checker

import mlang.core.concrete.{Name, NameRef}


sealed trait Closure {

  def apply(v: Value): Value = ???
}


case class Avg(head: Seq[Value], tail: Seq[Value] => Avg)


sealed trait Value {
  def application(v: Value): Value = ???
  def projection(name: NameRef): Value = ???
}



object Value {
  type Stuck = Value

  case class Universe(level: Int) extends Value

  case class Function(domain: Value, codomain: Closure) extends Value

  // TODO should have a field: recursive, and it must be recursive
  case class Record(names: Seq[Name], initial: Avg) extends Value
  // TODO should have a field: recursive, and it must be recursive, also in case of indexed, use Constructor instead of value
  sealed trait Constructor
  object Constructor {
    // TODO add index, and path
    case class Constant() extends Constructor
    case class Normal(parameter: Value) extends Constructor
  }
  case class Sum(branches: Map[Name, Constructor]) extends Value

  case class Lambda(closure: Closure) extends Value
  case class Make(values: Seq[Value]) extends Value
  case class Construct(name: Name, v: Value) extends Value

  case class RecursiveReference(var value: Value, name: NameRef) extends Value
  case class Reference(value: Value, name: Name) extends Value
  case class OpenReference(id: Long, name: Name) extends Value

  case class Application(lambda: Stuck, argument: Value) extends Value
  case class PatternElimination(lambda: Value, argument: Stuck) extends Value
  case class Projection(make: Stuck, field: Name) extends Value
}

