package mlang.editor

import mlang.utils._


enum TypeVariant {
  case Regular
  case Bold
  case Italic
}

trait Event {

}

case class Draw(string: Unicode)


trait EditorPlatform {
  def measure(unicode: Unicode, size: Int, typeface: TypeVariant): Point
  def draws(dw: Seq[Draw]): Unit
}

class Editor(platform: EditorPlatform) {
  def windowSize(width: Int, height: Int): Unit
  def update(events: Seq[Event]): Unit
}
