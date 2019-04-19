package mlang.core

import mlang.name._


sealed trait Pattern

object Pattern {
  case object Atom extends Pattern
  case class Make(names: Seq[Pattern]) extends Pattern // TODO named patterns?
  case class Construct(name: Tag, pattern: Seq[Pattern]) extends Pattern
}
