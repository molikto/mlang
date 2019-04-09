package mlang.core.utils

object debug {

 def apply(s: => Any) = if (false) println(s"debug: $s")
}
