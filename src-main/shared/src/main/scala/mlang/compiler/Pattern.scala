package mlang.compiler



sealed trait PatternExtractException extends CompilerException

object PatternExtractException {
  case class MakeWrongSize() extends PatternExtractException
  case class MakeIsNotRecordType() extends PatternExtractException
  case class ConstructUnknownName() extends PatternExtractException
  case class ConstructWrongSize() extends PatternExtractException
  case class ConstructNotSumType() extends PatternExtractException
}


sealed trait Pattern {
  def atomCount: Int = this match {
    case Pattern.Atom => 1
    case Pattern.Make(names) => names.map(_.atomCount).sum
    case Pattern.Construct(_, pattern) => pattern.map(_.atomCount).sum
  }
}

object Pattern {
  case object Atom extends Pattern
  case class Make(names: Seq[Pattern]) extends Pattern
  case class Construct(name: Int, pattern: Seq[Pattern]) extends Pattern
}
