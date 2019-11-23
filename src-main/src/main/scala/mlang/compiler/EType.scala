package mlang.compiler

import mlang.utils._

sealed trait EType

// the idea being types has part of information that only used by elaboration process, ignore them in core theory,
// and make them modifiable (by type cast)
object EType {
  case class Function(implicitt: Boolean) extends EType
  object Function {
    val Implicit = Function(true)
    val NonImplicit = Function(false)
    def get(i: Boolean): Function = if (i) Implicit else NonImplicit
  }
  case class Record(names: Seq[Name], implicits: Seq[Boolean]) extends EType
  case class Sum(contextual: Boolean, names: Seq[Name], implicits: Seq[Seq[Boolean]]) extends EType
}