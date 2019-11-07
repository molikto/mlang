package mlang.utils

class Printer(val prefix: String, val threshold: Int, val level: Int, color: Option[fansi.EscapeAttr]) {
  def enabled(level: Int): Boolean = level >= threshold
  val enabled = level >= threshold
  def apply(s: => Any, l: Int = level) = if (l >= threshold) {
    val p = color match {
      case Some(value) => value.apply(prefix)
      case None => fansi.Str(prefix)
    }
    println(p.toString() + ": " + s)
  }
}
object debug extends Printer("debug", 2, 0, None)

object info extends Printer("info",0, 0, Some(fansi.Color.LightBlue))

object warn extends Printer("warn", 0, 0, Some(fansi.Color.LightRed))
