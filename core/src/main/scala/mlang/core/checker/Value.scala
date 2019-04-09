package mlang.core.checker

import mlang.core.concrete.{Name, NameRef}


sealed trait Closure {

  def apply(v: Value): Value = ???
}


sealed trait MultiClosure {
  def apply(v: Seq[Value]): Value = ???
}

case class RecordNode(name: Name, dependencies: Seq[NameRef]) extends MultiClosure {
}



sealed trait Value {
  def app(v: Value): Value = ???
  def project(name: NameRef): Value = ???
}



object Value {
  type Stuck = Value

  case class Universe(level: Int) extends Value

  case class RecursiveReference(var value: Value, name: NameRef) extends Value
  case class Reference(value: Value, name: Name) extends Value
  case class OpenReference(id: Long, name: Name) extends Value

  case class Function(domain: Value, codomain: Closure) extends Value
  /**
    * this lambda is transparent on the arguments
    */
  case class Lambda(closure: Closure) extends Value
  case class Application(lambda: Stuck, argument: Value) extends Value

  // TODO should have a field: recursive, and it must be recursive
  // TODO record should have a type
  /**
    */
  case class Record(nodes: Seq[RecordNode]) extends Value {
    assert(nodes.isEmpty || nodes.head.dependencies.isEmpty)
    def make: Value = ???
    def makeType: Value = ???
    def projectedType(values: Seq[Value], name: NameRef): Value = ???
  }
  case class Make(values: Seq[Value]) extends Value
  case class Projection(make: Stuck, field: Name) extends Value

  case class Construct(name: Name, vs: Seq[Value]) extends Value
  // TODO sum should have a type, it can be indexed, so a pi type ends with type_i
  // TODO should have a field: recursive, and it must be recursive, also in case of indexed, use Constructor instead of value
  case class Constructor(name: Name, nodes: Seq[MultiClosure]) {
    def make: Value = ???
    def makeType: Value = ???
  }
  case class Sum(constructors: Seq[Constructor]) extends Value

  sealed trait Pattern {
  }
  case class Case(pattern: Pattern, closure: MultiClosure)
  case class PatternLambda(cases: Seq[Case]) extends Value
}

