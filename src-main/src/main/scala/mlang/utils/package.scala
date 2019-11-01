package mlang

import scala.collection.mutable

package object utils {

  def logicError(): Nothing = logicError("no additional info provided")

  def logicError(additionalInfo: String) = throw new IllegalArgumentException(s"This state is considered a logic error (${additionalInfo})")

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
