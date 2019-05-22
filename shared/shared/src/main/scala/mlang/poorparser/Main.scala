package mlang.poorparser

import java.io.File

import mlang.core.TypeChecker
import mlang.utils.Benchmark

object Main extends Parser {

  def main(args: Array[String]): Unit = {
    val checker = TypeChecker.empty
    new File("library").listFiles(_.getName.endsWith(".poor")).sortBy(_.getName).foreach(f => {
      val res = parse(scala.io.Source.fromFile(f).getLines().mkString("\n"))
      res match {
        case Success(result, next) =>
          if (next.atEnd) checker.check(result)
          else throw new Exception("Parse failed with last " + result.declarations.lastOption + "and remaining " + next.rest.toString)
        case NoSuccess(msg, _) =>
          throw new Exception(s"Parse failed with $msg")
      }
    })
    Benchmark.report()
  }
}
