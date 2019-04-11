package mlang.core

import mlang.core.Name.Ref
import mlang.core.utils.Text

case class Name(main: Text) {

  def intersect(name: Name): Boolean = name.main == main
  def by(name: Ref): Boolean = name == main
  def ref: Name.Ref = main

  override def equals(obj: Any): Boolean = {
    obj match {
      case o: Name => o.main == main
      case _ => throw new IllegalArgumentException("Should not compare name to other stuff")
    }
  }
}

object Name {
  type Ref = Text

  object Ref {
    val empty: Ref = Text("")

    val make: Ref = Text("make")
  }

  type Opt = Option[Name]
}
