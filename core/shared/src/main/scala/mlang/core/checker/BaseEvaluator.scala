package mlang.core.checker

import scala.collection.mutable


trait Holder {
  def value(c: Context, vs: Seq[Value], cs: Seq[Value.Closure], ps: Seq[Pattern]): Value
}

trait BaseEvaluator extends Context {


  private val existingValues = mutable.ArrayBuffer[Value]()
  private val existingClosures = mutable.ArrayBuffer[Value.Closure]()
  private val existingPatterns = mutable.ArrayBuffer[Pattern]()

  protected def extractFromHolder(h: Holder): Value = {
    val res = h.value(this, existingValues, existingClosures, existingPatterns)
    res
  }

  protected def tunnel(v: Value): String = {
    val i = existingValues.size
    existingValues.append(v)
    return s"vs($i)"
  }

  protected def tunnel(v: Value.Closure): String = {
    val i = existingClosures.size
    existingClosures.append(v)
    return s"cs($i)"
  }

  protected def tunnel(v: Pattern): String = {
    val i = existingPatterns.size
    existingPatterns.append(v)
    return s"ps($i)"
  }

  protected def platformEval(value: Abstract): Value

  protected def eval(term: Abstract): Value = {
    term match {
      case Abstract.Reference(up, index, name) => get(up, index).value.get
      case _ => platformEval(term)
    }
  }
}
