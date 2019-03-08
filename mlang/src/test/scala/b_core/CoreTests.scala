package b_core

import sun.applet.Main
import utest._
import z_main.MainMain

object CoreTests extends TestSuite {

  val tests = Tests {
    def run(a: String) = {
      new MainMain().main(a)
    }

    'invalidPi - {
      intercept[Exception] {
        run("what: type = (type) => what;")
      }
    }
  }
}