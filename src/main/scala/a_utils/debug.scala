package a_utils




object debug {

  def apply(s: => Any) = if (true) println(s"debug: $s")

  def display(a: Any) = println(s"display: $a")
}
