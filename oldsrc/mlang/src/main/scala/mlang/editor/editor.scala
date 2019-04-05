package mlang.editor

import mlang.utils._


enum TypefaceVariant {
  case Regular
  case Bold
  case Italic
}

trait Event {

}

sealed case class AbstractTextRun(unicode: Unicode, size: Int, typeface: TypefaceVariant)

sealed case class MeasuredTextInfo(width: Int, top: Int, bottom: Int)

sealed case class Draw(string: Unicode)


trait Platform {
  def measure(measureable: AbstractTextRun): MeasuredTextInfo
  def draws(dw: Seq[Draw]): Unit
}

class Editor(platform: Platform, size: Point) {

  def update(events: Seq[Event]): Unit = {
    ???
  }
}
