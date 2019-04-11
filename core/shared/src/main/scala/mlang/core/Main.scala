package mlang.core

import mlang.core.checker.TypeChecker
import mlang.core.concrete._
import mlang.core.concrete.Term._

object Main {
  implicit def strToRef(s: String) = Reference(s)
  def pi (a: Term, b: Term) = Function(a, "", b)
  def main(args: Array[String]): Unit = {
    TypeChecker.empty.checkModule(Module(Seq(
      Declaration.Define("bool", None, Sum(
        Seq(Constructor("true", Seq.empty),
        Constructor("false", Seq.empty)
      ))),
      Declaration.Define("not", Some(pi("bool", "bool")),
        PatternLambda(Seq(
          Case(Pattern.Constructor("true", Seq.empty), Projection("bool", "false")),
          Case(Pattern.Constructor("false", Seq.empty), Projection("bool", "true"))
        ))),
      Declaration.Define("bool_pair", None,
        Record(Seq(
          NameType("_1", "bool"),
          NameType("_2", "bool")
        ))),
    )))
  }
}
