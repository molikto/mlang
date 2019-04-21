package mlang.core

import mlang.name._


sealed trait Pattern {
  def atomCount: Int = this match {
    case Pattern.Atom => 1
    case Pattern.Make(names) => names.map(_.atomCount).sum
    case Pattern.Construct(_, pattern) => pattern.map(_.atomCount).sum
  }

}

object Pattern {
  case object Atom extends Pattern
  case class Make(names: Seq[Pattern]) extends Pattern // TODO named patterns?
  case class Construct(name: Tag, pattern: Seq[Pattern]) extends Pattern
}
