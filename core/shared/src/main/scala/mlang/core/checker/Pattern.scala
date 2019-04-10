package mlang.core.checker

import mlang.core.concrete.NameRef


sealed trait Pattern

object Pattern {
  case object Atom extends Pattern
  case class Make(names: Seq[Pattern]) extends Pattern // TODO named patterns?
  case class Constructor(name: NameRef, pattern: Seq[Pattern]) extends Pattern
}
