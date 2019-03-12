package mlang.editor

import mlang.utils._


enum TypefaceVariant {
  case Regular
  case Bold
  case Italic
}

trait Event {

}

case class AbstractTextRun(unicode: Unicode, size: Int, typeface: TypefaceVariant)

case class MeasuredTextInfo(width: Int, top: Int, bottom: Int)

case class Draw(string: Unicode)


trait Platform {
  def measure(measureable: Measureable): MeasuredTextInfo
  def draws(dw: Seq[Draw]): Unit
}

class Editor(platform: Platform, size: Point) {

  def update(events: Seq[Event]): Unit = {
    ???
  }
}
