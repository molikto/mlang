package mlang.compiler



sealed trait PatternExtractException extends CompilerException

object PatternExtractException {
  case class WrongSize() extends PatternExtractException
  case class NotExpectingImplicit() extends PatternExtractException
  case class MakeIsNotRecordType() extends PatternExtractException
  case class ConstructUnknownName() extends PatternExtractException
  case class ConstructNotSumType() extends PatternExtractException
  case class NonAtomicPatternForDimension() extends PatternExtractException
  case class ImplicitPatternForDimension() extends PatternExtractException
  case class HitPatternMatchingShouldBeAtRoot() extends PatternExtractException
}


sealed trait Pattern {

  private def sum(a: Seq[(Int, Int)]) = (a.map(_._1).sum, a.map(_._2).sum)
  def atomCount: (Int, Int) = this match {
    case Pattern.GenericValue => (1, 0)
    case Pattern.GenericDimension => (0, 1)
    case Pattern.Make(names) => sum(names.map(_.atomCount))
    case Pattern.Construct(_, pattern) => sum(pattern.map(_.atomCount))
  }
}

// FIXME(PATTERN) support implicit variables
object Pattern {
  case object GenericValue extends Pattern
  case object GenericDimension extends Pattern
  case class Make(names: Seq[Pattern]) extends Pattern
  case class Construct(name: Int, pattern: Seq[Pattern]) extends Pattern
}
