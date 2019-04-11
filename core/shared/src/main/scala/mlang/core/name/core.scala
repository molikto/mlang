package mlang.core

import mlang.core.utils.Text

package object name {


  type Ref = Text
  type Tag = Text

  object Ref {
    val empty: Ref = Text("")

    val make: Ref = Text("make")
  }

}
