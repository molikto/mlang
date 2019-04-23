package mlang.utils

class Printer(val prefix: String, val enabled: Boolean) {
 def apply(s: => Any) = if (enabled) println(s"$prefix: $s")
}
object debug extends Printer("debug", true)

object info extends Printer("info",true)
