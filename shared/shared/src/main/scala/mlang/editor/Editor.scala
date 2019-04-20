package mlang.editor

import mlang.utils._


case class StyledText(text: Text)
case class StyledTextMeasurement(ascent: Float, descent: Float, width: Float)

abstract class Editor() {

  def width: Float
  def height: Float
  def measure(text: StyledText): StyledTextMeasurement

  def onDimensionChanged(): Unit = {
  }
}