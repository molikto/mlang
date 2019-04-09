package mlang.core


import mlang.core.utils._

/**
  * the minimal syntax a editor can provide, because of type directed resolution, the elimination rules is always different with values
  */
package object concrete {

  //case class Name(short: Text, long: Text)
  type Name = Text
  type NameRef = Text

  object NameRef {
    val make: NameRef = Text("make")
  }
}


