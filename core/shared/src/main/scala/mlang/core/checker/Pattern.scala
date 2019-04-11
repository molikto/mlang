package mlang.core.checker

import mlang.core.Name


sealed trait Pattern

object Pattern {
  case object Atom extends Pattern
  case class Make(names: Seq[Pattern]) extends Pattern // TODO named patterns?
  case class Constructor(name: Name.Ref, pattern: Seq[Pattern]) extends Pattern
}
