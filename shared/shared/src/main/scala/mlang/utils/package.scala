package mlang

import scala.collection.mutable

package object utils {

  def logicError() = throw new IllegalArgumentException("This state is considered a logic error")

  implicit class Text(val s: String) extends AnyVal {
    def string: String = s
    override def toString: String = s.toString
    def isEmpty: Boolean = s.isEmpty
    def nonEmpty: Boolean = !s.isEmpty
  }

  def fillTo[T](a: mutable.ArrayBuffer[T], i: Int) : Unit = {
    while (i >= a.size) a.append(null.asInstanceOf[T])
  }
}
