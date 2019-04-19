package mlang.utils

object debug {

 def apply(s: => Any) = if (true) println(s"debug: $s")
}
