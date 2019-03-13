package mlang.utils



  def debug(s: => Any) = if (false) println(s"debug: $s")

  def display(a: Any) = println(s"display: $a")