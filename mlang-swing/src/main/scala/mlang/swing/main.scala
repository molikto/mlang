package mlang.swing

import java.awt._
import javax.swing._
import mlang.editor._
import mlang.utils._

class Main extends Platform {

  UIManager.setLookAndFeel( UIManager.getSystemLookAndFeelClassName())

  val frame = new JFrame("mlang")
  frame.setSize(500, 500)

  val content = new JPanel(null)

  val scroller = new JScrollPane(content)

  def scrollbarWidth = scroller.getVerticalScrollBar().getSize.getWidth.toInt

  scroller.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_NEVER)
  scroller.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS)

  content.setSize(frame.getWidth - scrollbarWidth, 1000)
  

  frame.getContentPane.add(scroller)

  def draws(dw: Seq[Draw]) = {
    ???
  }

  def measure(measureable: AbstractTextRun) = {
    ???
  }

  def newEvents() = {
    ???
  }

  frame.setVisible(true)
  frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE)
}

object Main {

  def main(args: Array[String]): Unit = {
    new Main()
  }


}