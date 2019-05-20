package mlang.utils

class Printer(val prefix: String, val threshold: Int, val level: Int) {
  def enabled(level: Int): Boolean = level >= threshold
  val enabled = level >= threshold
  def apply(s: => Any, l: Int = 0) = if (l >= threshold) println(s"$prefix: $s")
}
object debug extends Printer("debug", 1, 0)

object info extends Printer("info",0, 0)
