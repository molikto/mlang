package mlang.core

import scala.collection.mutable


trait Holder {
  def value(c: Context, r: Reduction, rs: Seq[Value], vs: Seq[Value], cs: Seq[Value.Closure], ps: Seq[Pattern]): Value
}

trait BaseEvaluator extends Context {


  private val vs = mutable.ArrayBuffer[Value]()
  private val cs = mutable.ArrayBuffer[Value.Closure]()
  private val ps = mutable.ArrayBuffer[Pattern]()

  protected def extractFromHolder(h: Holder, reduction: Reduction, map: Seq[Value]): Value = {
    val res = h.value(this, reduction, map, Seq.empty ++ vs, Seq.empty ++ cs, Seq.empty ++ ps)
    vs.clear()
    cs.clear()
    ps.clear()
    res
  }

  protected def tunnel(v: Value): String = {
    val i = vs.size
    vs.append(v)
    s"vs($i)"
  }

  protected def tunnel(v: Value.Closure): String = {
    val i = cs.size
    cs.append(v)
    s"cs($i)"
  }

  protected def tunnel(v: Pattern): String = {
    val i = ps.size
    ps.append(v)
    s"ps($i)"
  }

  protected def platformEval(value: Abstract, reduction: Reduction ): Value
  protected def platformEvalRecursive(terms: Map[Int, Abstract], reduction: Reduction): Map[Int, Value]

  protected def evalOpenTermReferenceAsReference(i: Int, index: Int): Value = {
    getTerm(i, index).value match {
      case o: Value.OpenReference => o // a formal argument in context
      case v => Value.Reference(v, 0) // a definition in context, cannot be recursive
    }
  }

  protected def evalMutualRecursive(terms: Map[Int, Abstract], reduction: Reduction /* REDUCTION */): Map[Int, Value] = {
    val ret = platformEvalRecursive(terms, reduction)
    assert(ret.forall(_._2 != null))
    ret
  }

  protected def eval(term: Abstract, reduction: Reduction /* REDUCTION */): Value = {
    term match {
      case Abstract.TermReference(up, index, _) => evalOpenTermReferenceAsReference(up, index).deref(reduction)
      case Abstract.Universe(i) => Value.Universe(i)
      case _ =>
        val ret = platformEval(term, reduction)
        assert(ret != null)
        ret
    }
  }
}
