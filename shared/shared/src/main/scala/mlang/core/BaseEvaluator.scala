package mlang.core

import mlang.utils.{Benchmark, debug}

import scala.collection.mutable

case class PlatformEvaluatorException(src: String, cause: Throwable)
    extends Exception(s"Src: $src", cause) with CoreException

trait Holder {
  def value(c: Context, rs: Seq[Value], vs: Seq[Value], cs: Seq[Value.Closure], ps: Seq[Pattern]): Value
}

// the evaluator perform a direct translation of abstract terms under a context to a
// context independent value, the only thing that is complicated is how to handle references and recursion
// recursion is represented by object graph where recursion handles inside a closure
trait BaseEvaluator extends Context {


  private val vs = mutable.ArrayBuffer[Value]()
  private val cs = mutable.ArrayBuffer[Value.Closure]()
  private val ps = mutable.ArrayBuffer[Pattern]()

  protected def extractFromHolder(h: Holder, map: Seq[Value]): Value = {
    val res = h.value(this, map, vs.clone(), cs.clone(), ps.clone())
    if (debug.enabled) {
      for (v <- vs.indices) debug(s"v$v: ${vs(v)}")
      for (v <- ps.indices) debug(s"v$v: ${ps(v)}")
    }
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

  protected def platformEval(value: Abstract): Value
  protected def platformEvalRecursive(terms: Map[Int, Abstract]): Map[Int, Value]

  protected def evalTermReferenceAsReference(i: Int, index: Int, closed: Boolean): Value = {
    getTerm(i, index).value match {
      case o: Value.Generic =>
        assert(!closed)
        o // a formal argument in context
      case v =>
        assert(closed)
        Value.Reference(v) // a definition in context, cannot be recursive
    }
  }

  protected def evalMutualRecursive(terms: Map[Int, Abstract]): Map[Int, Value] = {
    Benchmark.Eval {
      val ret = platformEvalRecursive(terms)
      assert(ret.forall(_._2 != null))
      ret
    }
  }

  protected def evalClosureTemp(a: Abstract.AbsClosure): Value.AbsClosure = {
    eval(Abstract.PathLambda(a)).asInstanceOf[Value.PathLambda].body
  }

  protected def eval(term: Abstract): Value = {
    Benchmark.Eval {
      term match {
        case Abstract.TermReference(up, index, closed) => evalTermReferenceAsReference(up, index, closed)
        case Abstract.Universe(i) => Value.Universe(i)
        case _ =>
          val ret = platformEval(term)
          assert(ret != null)
          ret
      }
    }
  }
}
