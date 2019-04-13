package mlang.core.checker

import scala.collection.mutable


trait Holder {
  def value(c: Context, r: Reduction, rr: Map[Int, Value], vs: Seq[Value], cs: Seq[Value.Closure], ps: Seq[Pattern]): Value
}

trait BaseEvaluator extends Context {


  private val vs = mutable.ArrayBuffer[Value]()
  private val cs = mutable.ArrayBuffer[Value.Closure]()
  private val ps = mutable.ArrayBuffer[Pattern]()

  protected def extractFromHolder(h: Holder, reduction: Reduction, map: Map[Int, Value]): Value = {
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

  protected def evalOpenAsReference(i: Int, index: Int): Value = {
    get(i, index).value match {
      case o: Value.OpenReference => o // a formal argument in context
      case v => Value.Reference(v) // a definition in context
    }
  }

  protected def evalMutualRecursive(terms: Map[Int, Abstract], reduction: Reduction = Reduction.Default): Map[Int, Value] = {
    platformEvalRecursive(terms, reduction)
  }

  protected def eval(term: Abstract, reduction: Reduction = Reduction.Default): Value = {
    term match {
      case Abstract.Reference(up, index, _) => evalOpenAsReference(up, index).deref(reduction)
      case Abstract.Universe(i) => Value.Universe(i)
      case _ => platformEval(term, reduction)
    }
  }
}
