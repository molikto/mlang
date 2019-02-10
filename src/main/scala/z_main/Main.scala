package z_main

import a_utils.debug
import b_core.TypeChecker
import c_surface_syntax.{Parser, surface}
import d_elaborator.Elaborator


object Main extends TypeChecker with Elaborator {

  val parser = new Parser {}
  def main(args: Array[String]): Unit = {
    val txt = io.Source.fromFile(args(0)).getLines().mkString("\n")
    parser.parse(txt) match {
      case parser.Success(parsed: Seq[surface.Definition], next) =>
        if (!next.atEnd) {
          throw new Exception(s"Parse failed with remaining ${next.source.toString.drop(next.offset)}")
        } else {
          debug(parsed)
          val elaborated = elaborate(c_surface_syntax.surface.Definitions(parsed))
          debug(elaborated)
          check(elaborated)
          debug("Finished")
        }
      case parser.NoSuccess(msg, next) =>
        throw new Exception(s"Parse failed $msg")
    }
  }
}
