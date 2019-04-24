package mlang.utils

object Benchmark {


  case class Phase(name: String, including: Seq[Phase] = Seq.empty) {

    var t : Long = 0
    @inline def apply[T](a: => T): T = {
      val t0 = System.currentTimeMillis()
      val res = a
      t += (System.currentTimeMillis() - t0)
      res
    }

    def self: Long = t - including.map(_.t).sum

    def report(indent: Int): Unit = {
      info(s"${(0 until (indent * 2)).map(_ => ' ').mkString("")}Phase $name self time: ${self}ms, total time ${t}ms")
      including.foreach(_.report(indent + 1))
    }
  }

  val ConversionChecking = Phase("conversion checking")

  val HoasCompile = Phase("hoas compile")

  val Eval = Phase("eval", Seq(HoasCompile))

  val Reify = Phase("reify")

  val TypeChecking = Phase("type checking", Seq(Eval, ConversionChecking, Reify))

  val Parsing = Phase("parsing")

  private val all = Seq(Parsing, TypeChecking)

  def report(): Unit = {
    all.foreach(_.report(0))
  }
}
