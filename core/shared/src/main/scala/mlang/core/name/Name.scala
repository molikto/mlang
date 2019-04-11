package mlang.core.name

import mlang.core.utils.Text


case class Name(main: Text) {

  def intersect(name: Name): Boolean = name.main == main
  def by(name: Text): Boolean = name == main
  def refSelf: Ref = main

  def asRef: Option[Ref] = Some(main)


  override def toString: String = main.toString

  override def equals(obj: Any): Boolean = {
    obj match {
      case o: Name => o.main == main
      case _ => throw new IllegalArgumentException("Should not compare name to other stuff")
    }
  }
}

object Name {
  val empty: Name = Name("")

  type Opt = Option[Name]
}
