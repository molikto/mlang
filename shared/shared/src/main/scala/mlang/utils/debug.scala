package mlang.utils

object debug {

 val enabled = true
 def apply(s: => Any) = if (enabled) println(s"debug: $s")
}
