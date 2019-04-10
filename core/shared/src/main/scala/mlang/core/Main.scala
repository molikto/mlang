package mlang.core

import mlang.core.checker.TypeChecker
import mlang.core.concrete._
import mlang.core.concrete.Term._

object Main {
  def main(args: Array[String]): Unit = {
    TypeChecker.empty.checkModule(Module(Seq(
      Declaration.Define("bool", Sum(
        Seq(Constructor("true", Seq.empty),
        Constructor("false", Seq.empty)
      )), None)
    )))
  }
}
