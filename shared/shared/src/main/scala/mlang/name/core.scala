package mlang

import mlang.utils.Text

package object name {


  type Ref = Text
  type Tag = Text

  object Ref {
    val empty: Ref = Text("")
  }

}
