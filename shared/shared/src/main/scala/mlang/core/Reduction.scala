package mlang.core


/**
  * app = Some(_) means evaluate a beta redex, and the closure itself will be evaluated using the reduction method given
  */
case class Reduction(
    var app: Option[Reduction],
    project: Boolean,
    var papp: Option[Reduction],
    deref: Int,
    delet: Boolean
)

object Reduction {
  object Deref {
    val No = 0
    val NonRecursive = 1
    // this means if the
    //val ProgressRecursive = 2
    val All = 3
  }

  // TODO proof this is ok with recursive definitions
  val Default: Reduction = {
    val r = Reduction(null, true, null, Deref.All, true)
    r.app = Some(r)
    r.papp = Some(r)
    r
  }
}
