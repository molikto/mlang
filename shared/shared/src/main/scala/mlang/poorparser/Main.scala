package mlang.poorparser

import java.io.File

import mlang.core.TypeChecker
import mlang.utils.{Benchmark, debug, info}

object Main extends Parser {

  def test(a: File, shouldFails: Boolean) = {
    a.listFiles(_.getName.endsWith(".poor")).sortBy(_.getName).foreach(f => {
      info(s"testing ${a.getName}/${f.getName}")
      val s = src(f)
      val module = parseOrThrow(s)
      var fails = ""
      val exp = if (shouldFails) {
        assert(s.startsWith("// "))
        s.takeWhile(_ != '\n').drop(3)
      } else {
        ""
      }
      var cause: Exception = null
      try {
        TypeChecker.topLevel().check(module)
      } catch {
        case e: Exception =>
          cause = e
          fails = e.getClass.getSimpleName
      }
      if (fails != exp) {
        val msg = if (shouldFails) {
          if (fails == "") {
            "expecting to fail"
          } else {
            s"expecting $exp"
          }
        } else {
          "not expecting it to fail"
        }
        throw new Exception(s"Test failure with in ${a.getName}/${f.getName}, $msg", cause)
      }
    })
  }

  def library(file: File): Unit = {
    var checker = TypeChecker.topLevel()
    def rec(prefix: String, file: File): Unit = {
      file.listFiles().sortBy(_.getName).foreach(f => {
        val name = prefix + f.getName
        if (f.isDirectory) {
          info(s"entering folder $name")
          rec(name + "/", f)
        } else if (f.getName.endsWith(".poor")) {
          info(s"checking file $name")
          checker = checker.check(parseOrThrow(src(f)))
        }
      })
    }
    rec("", file)
    Benchmark.reportAndReset()
  }

  def main(args0: Array[String]): Unit = {
    val args = args0.filter(a => a == "library" || a == "tests")
    val runLibrary = args.isEmpty || args.contains("library")
    val runTests = args.isEmpty || args.contains("tests")
    if (args.isEmpty) debug("Usage: pass argument library or/and tests to only run library or only run tests")
    if (runLibrary) {
      library(new File("library"))
    }
    if (runTests) {
      val tests = new File("tests")
      test(new File(tests, "exception"), true)
      test(new File(tests, "pass"), false)
      Benchmark.reportAndReset()
    }
  }
}
