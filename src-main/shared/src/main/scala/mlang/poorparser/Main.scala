package mlang.poorparser

import java.io.File

import mlang.compiler.Concrete
import mlang.compiler.Elaborator
import mlang.utils.{Benchmark, debug, info, warn}

object Main extends Parser {

  def test(a: File, shouldFails: Boolean) = {
    if (a.exists()) {
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
          Elaborator.topLevel().check(module)
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
  }

  def library(file: File): Unit = {
    val checker = Elaborator.topLevel()
    def rec(prefix: String, file: File): Seq[(String, Concrete.Module)] = {
      file.listFiles().sortBy(_.getName).toSeq.flatMap(f => {
        val name = prefix + f.getName
        if (f.isDirectory) {
          rec(name + "/", f)
        } else if (f.getName.endsWith(".poor")) {
          try {
            Seq((name, parseOrThrow(src(f))))
          } catch {
            case e: Exception =>
              e.printStackTrace()
              warn(s"Parsing error, ignoring file $name")
              Seq.empty
          }
        } else {
          Seq.empty
        }
      })
    }
    val modules = rec("", file)
    checker.check(Concrete.Module(modules.flatMap(_._2.declarations)))
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
      test(new File(tests, "exception_now"), true)
      test(new File(tests, "pass_now"), false)
      test(new File(tests, "exception"), true)
      test(new File(tests, "pass"), false)
      Benchmark.reportAndReset()
    }
  }
}
