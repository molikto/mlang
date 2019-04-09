package mlang.core.checker

import mlang.core.concrete.{Name, NameRef}


sealed trait Abstract

object Abstract {
  case class AbstractReference(up: Int, index: Int, name: NameRef) extends Abstract

  case class Function(domain: Abstract, codomain: Abstract) extends Abstract

  case class Lambda(closure: Abstract) extends Abstract

  case class Application(left: Abstract, right: Abstract) extends Abstract

  case class RecordNode(name: Name, typ: Abstract)
  case class Record(nodes: Seq[RecordNode]) extends Abstract

  case class RecordMaker(record: Abstract) extends Abstract

  case class Projection(left: Abstract, field: NameRef) extends Abstract

  case class Constructor(name: Name, params: Seq[Abstract])
  case class Sum(constructors: Seq[Constructor]) extends Abstract

  case class SumMaker(sum: Abstract, field: NameRef) extends Abstract

  case class Let(definitions: Seq[Abstract], in: Abstract) extends Abstract

  sealed trait Pattern

  object Pattern {
    case object Atom extends Pattern
    case class Make(names: Seq[Pattern]) extends Pattern // TODO named patterns?
    case class Constructor(name: NameRef, pattern: Seq[Pattern]) extends Pattern
  }

  case class Case(pattern: Pattern, body: Abstract)
  case class PatternLambda(cases: Seq[Case]) extends Abstract
}
