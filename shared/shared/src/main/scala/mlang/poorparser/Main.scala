package mlang.poorparser

import java.io.File

import mlang.core.TypeChecker
import mlang.utils.{Benchmark, debug}

object Main extends Parser {

  def test(a: File, shouldFails: Boolean) = {
    a.listFiles(_.getName.endsWith(".poor")).foreach(f => {
      debug(s"Testing ${a.getName}/${f.getName}", 5)
      val module = parseOrThrow(f)
      var fails = false
      var cause: Exception = null
      try {
        TypeChecker.topLevel.check(module)
      } catch {
        case e: Exception =>
          cause = e
          fails = true
      }
      if (fails != shouldFails) {
        throw new Exception(s"Test failure with in ${a.getName}/${f.getName}", cause)
      }
    })
  }

  def library(file: File): Unit = {
    var checker = TypeChecker.topLevel
    def rec(prefix: String, file: File): Unit = {
      file.listFiles().sortBy(_.getName).foreach(f => {
        val name = prefix + f.getName
        if (f.isDirectory) {
          debug(s"Entering folder $name", 5)
          rec(name + "/", f)
        } else if (f.getName.endsWith(".poor")) {
          debug(s"Checking file $name", 5)
          checker = checker.check(parseOrThrow(f))
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
      test(new File(tests, "pass"), false)
      test(new File(tests, "exception"), true)
    }
    Benchmark.reportAndReset()
  }
}
