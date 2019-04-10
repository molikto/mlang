package mlang.core

import mlang.core.checker.TypeChecker
import mlang.core.concrete._

object Main {
  def main(args: Array[String]): Unit = {
    TypeChecker.empty.checkModule(Module(Seq(

    )))
  }
}
