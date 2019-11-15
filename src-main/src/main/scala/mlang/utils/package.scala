package mlang.utils

import scala.collection.mutable


def logicError(): Nothing = logicError("no additional info provided")

def logicError(additionalInfo: String) = throw new IllegalArgumentException(s"This state is considered a logic error (${additionalInfo})")

opaque type Text = String
object Text {
  def apply(s: String): Text = s
}
given (s: Text) {
  def string: String = s
  def toString: String = s.toString
  def isEmpty: Boolean = s.isEmpty
  def nonEmpty: Boolean = !s.isEmpty
}

def fillTo[T](a: mutable.ArrayBuffer[T], i: Int) : Unit = {
  while (i >= a.size) a.append(null.asInstanceOf[T])
}