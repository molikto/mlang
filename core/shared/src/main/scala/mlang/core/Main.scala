package mlang.core

import java.io.File

import mlang.core.checker.TypeChecker
import mlang.core.poorparser.Parser

object Main extends Parser {

  def main(args: Array[String]): Unit = {
    var checker = TypeChecker.empty
    new File("library").listFiles(_.getName.endsWith(".poor")).sortBy(_.getName).foreach(f => {
      val res = parse(scala.io.Source.fromFile(f).getLines().mkString("\n"))
      res match {
        case Success(result, next) =>
          if (next.atEnd) checker = checker.check(result)
          else throw new Exception("Parse failed with last " + result.declarations.lastOption + "and remaining " + next.rest.toString)
        case NoSuccess(msg, next) =>
          throw new Exception(s"Parse failed with $msg")
      }
    })
  }
}
