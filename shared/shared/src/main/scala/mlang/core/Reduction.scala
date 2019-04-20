package mlang.core


object Deref {
  val No = 0
  val NonRecursive = 1
  // this means if the
  //val ProgressRecursive = 2
  val All = 3
  val Normalize = 4
}


/**
  * app = Some(_) means evaluate a beta redex, and the closure itself will be evaluated using the reduction method given
  */
case class Reduction(
    var app: Option[Reduction],
    project: Boolean,
    var papp: Option[Reduction],
    deref: Int,
    delet: Boolean,
    demaker: Boolean,
    renormalize: Boolean
)

object Reduction {

  val Normalize: Reduction = {
    val r = Reduction(null, true, null, mlang.core.Deref.Normalize, true, true, true)
    r.app = Some(r)
    r.papp = Some(r)
    r
  }

  val No = Reduction(None, false, None, mlang.core.Deref.No, false, false, false)

  val Project = No.copy(project = true)

  object Deref {
    val All = No.copy(deref = mlang.core.Deref.All)
  }

  object App {
    val Once = No.copy(app = Some(No))
  }

  object Papp {
    val Once = No.copy(papp = Some(No))
  }

}
