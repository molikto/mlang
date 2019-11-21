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
        var cause: Throwable = null
        scala.util.Try(Elaborator.topLevel().check(module)) match {
          case scala.util.Success(v) =>
          case scala.util.Failure(e) =>
            fails = e.getClass.getSimpleName
            cause = e
        }
        if (fails != exp) {
          val msg = if (shouldFails) {
            if (cause != null) cause.printStackTrace()
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

  /*
  type Nat = (Boolean => Boolean) => (Boolean => Boolean)
  def n2: Nat = (f: Boolean => Boolean) => (b: Boolean) => f(b)
  def n5: Nat = (f: Boolean => Boolean) => (b: Boolean) => f(f(f(f(f(b)))))
  def mul(a: Nat, b: Nat) = (s: Boolean => Boolean) => (z: Boolean) => a(b(s))(z)
  def n10 = mul(n2,n5)
  def n100 = mul(n10,n10)
  def n10k = mul(n100,n100)
  def n10kb = mul(n100,mul(n10,n10))
  def n1M = mul(n10k,n100)
  def n1Mb = mul(n100,n10k)
  def n10M = mul(n1M,n10)
  def n10Mb = mul(n10,n1M)
  val t = System.currentTimeMillis()
  val a = n10M(x => x)(true)
  println(System.currentTimeMillis()- t)
  */

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
      test(new File(tests, "pass_now"), false)
      test(new File(tests, "pass"), false)
      test(new File(tests, "exception_now"), true)
      test(new File(tests, "exception"), true)
      Benchmark.reportAndReset()
    }
  }
}
