package z_main

import a_core.TypeChecker
import b_surface_syntax.Parser
import c_elaborator.Elaborator


class Main extends TypeChecker with Parser with Elaborator {

  def checkFile(a: String): Unit = {
    val txt = io.Source.fromFile(a).getLines().mkString("\n")
    check(transform(b_surface_syntax.surface.Definitions(parse(txt).get)))
  }
}
