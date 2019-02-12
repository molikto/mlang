package a_utils




object debug {

  def apply(s: => Any) = if (false) println(s"debug: $s")

  def display(a: Any) = println(s"display: $a")
}
