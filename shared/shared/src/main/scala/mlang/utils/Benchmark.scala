package mlang.utils

import scala.collection.mutable

object Benchmark {


  case class Instance(name: String, parent: Instance) {

    private[Benchmark] val childs = mutable.ArrayBuffer.empty[Instance]

    if (parent != null) parent.childs.append(this)

    var _t : Long = 0

    private def self: Long = _t - childs.map(_._t).sum

    def reportAndReset(indent: Int): Unit = {
      info(s"${(0 until (indent * 2)).map(_ => ' ').mkString("")}Phase $name self time: ${self}ms, total time ${_t}ms")
      childs.foreach(_.reportAndReset(indent + 1))
      _t = 0
    }
  }

  case class Phase(name: String, includes: Seq[Phase] = Seq.empty) {

    private val instances = mutable.ArrayBuffer.empty[Instance]

    private[Benchmark] def init(parent: Instance): Unit = {
      val instance = Instance(name, parent)
      includes.foreach(_.init(instance))
      instances.append(instance)
    }

    @inline def apply[T](a: => T): T = {
      val instance = instances.find(_.parent.eq(_current)).get
      val p = _current
      _current = instance
      val t0 = System.currentTimeMillis()
      val res = a
      instance._t += (System.currentTimeMillis() - t0)
      _current = p
      res
    }
  }

  val HoasCompile = Phase("hoas compile")

  val Eval = Phase("eval", Seq(HoasCompile))

  val Reify = Phase("reify")

  val Solve = Phase("solve", Seq(Reify, Eval))

  val Unify = Phase("unify", Seq(Solve))


  val TypeChecking = Phase("type checking", Seq(Eval, Unify, Reify))

  val Parsing = Phase("parsing")


  val all = Seq(TypeChecking, Parsing)

  private val root = Instance("", null)


  all.foreach(_.init(root))

  var _current: Instance = root

  def reportAndReset(): Unit = {
    root.childs.foreach(_.reportAndReset(0))
  }
}
