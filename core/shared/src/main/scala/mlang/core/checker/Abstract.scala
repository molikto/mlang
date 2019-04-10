package mlang.core.checker

import mlang.core.concrete.{Name, NameRef}


sealed trait Abstract {
}

object Abstract {
  case class Universe(i: Int) extends Abstract

  case class AbstractReference(up: Int, index: Int, name: NameRef) extends Abstract

  case class Function(domain: Abstract, codomain: Abstract) extends Abstract

  case class Lambda(closure: Abstract) extends Abstract

  case class Application(left: Abstract, right: Abstract) extends Abstract

  case class RecordNode(name: Name, typ: Abstract)
  case class Record(level: Int, nodes: Seq[RecordNode]) extends Abstract

  case class RecordMaker(record: Abstract) extends Abstract

  case class Projection(left: Abstract, field: Int) extends Abstract

  case class Constructor(name: Name, params: Seq[Abstract])
  case class Sum(level: Int, constructors: Seq[Constructor]) extends Abstract

  case class SumMaker(sum: Abstract, field: Int) extends Abstract

  case class Let(definitions: Seq[Abstract], in: Abstract) extends Abstract


  case class Case(pattern: Pattern, body: Abstract)
  case class PatternLambda(typ: Value.Closure, cases: Seq[Case]) extends Abstract
}
