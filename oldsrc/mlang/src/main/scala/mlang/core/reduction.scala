package mlang.core


case class Reduction(
  application: Boolean,
  split: Boolean,
  projection: Boolean,
  reference: Int)


object Reduction {
  // notice we DON'T expand recursive references!!!
  //
  // but --
  // a soft stuck is a closed recursive reference
  // the default reduction will ensure outermost is NOT a soft stuck
  // but it might be in other places, like in a sum type, the branches
  val Default = Reduction(true, true, true, 1)
}