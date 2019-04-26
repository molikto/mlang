package mlang.name

import mlang.utils.Text


// you create names by giving a non empty text or by referring to `Name.empty`, you test them by using method defined
// so an empty name is not something concerning the user of this class at all
case class Name(main: Text) {


  def source: String = s"Name"
  def intersect(name: Name): Boolean = this.main.nonEmpty && name.main.nonEmpty && name.main == main
  def by(name: Text): Boolean = this.main.nonEmpty && name.nonEmpty && name == main
  def refSelf: Ref = main
  def nonEmptyOrElse(hint: Name): Name = if (isEmpty) hint else this
  def isEmpty: Boolean = main.isEmpty

  def nonEmpty: Boolean = !isEmpty

  // what's the difference? sometimes, during parsing, a name can be the same thing as a ref, so this tests
  // if this name can actually representing a ref
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
}
