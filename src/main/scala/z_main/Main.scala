package z_main

import a_core.TypeChecker
import b_surface_syntax.Parser
import c_elaborator.Elaborator


object Main extends TypeChecker with Elaborator {

  val parser = new Parser {}
  def main(args: Array[String]): Unit = {
    val txt = io.Source.fromFile(args(0)).getLines().mkString("\n")
    val parsed = parser.parse(txt).get
    println(parsed)
    val elaborated = elaborate(b_surface_syntax.surface.Definitions(parsed))
    println(elaborated)
    check(elaborated)
  }
}
