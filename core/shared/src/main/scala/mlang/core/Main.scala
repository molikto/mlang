package mlang.core

import mlang.core.checker.TypeChecker
import mlang.core.concrete._
import mlang.core.concrete.Term._

object Main {
  implicit def strToRef(s: String) = Reference(s)
  def pi (a: Term, b: Term) = Function(a, "", b)
  def main(args: Array[String]): Unit = {
    TypeChecker.empty.checkModule(Module(Seq(
      Declaration.Define("bool", Sum(
        Seq(Constructor("true", Seq.empty),
        Constructor("false", Seq.empty)
      )), None),
      Declaration.Define("not",
        PatternLambda(Seq(
          Case(Pattern.Constructor("true", Seq.empty), Projection("bool", "false")),
          Case(Pattern.Constructor("false", Seq.empty), Projection("bool", "true"))
        ))
        , Some(pi("bool", "bool"))),
      Declaration.Define("bool_pair",
        Record(Seq(
          NameType("_1", "bool"),
          NameType("_2", "bool")
        ))
        , None),
    )))
  }
}
