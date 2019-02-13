package b_core

import b_core.Value.VP

import scala.collection.mutable


/**
  * a value compare class that handles recursive values
  *
  * in Mini-TT the comparing of values is done by readback. but this can be inefficient
  * because there are a lot of opportunities to stop early. this function compare values in
  * normal form structurally.
  *
  * using the congruence rules of lambda terms, lambda equality is done by applying the closure
  * to a generic value. to avoid infinite unfolding of lambda terms, this evaluation will not
  * unfold definitional equalities
  *
  */
// LATER compare with others
class CompareValue(a0: Value, b0: Value) {

  private val assumptions = new mutable.HashMap[Value, mutable.Set[Value]] with mutable.MultiMap[Value, Value]

  import Value.newUniqueId

  private def equalMvv(m1: Map[String, VP], m2: Map[String, VP]): Boolean = {
    m1.keySet == m2.keySet && m1.forall(pair => {
      val k = pair._1
      val a = pair._2
      val b = m2(k)
      equal(a, b)
    })
  }

  private def equalMv(m1: Map[String, Value], m2: Map[String, Value]): Boolean = {
    m1.keySet == m2.keySet && m1.forall(pair => {
      val k = pair._1
      val a = pair._2
      val b = m2(k)
      equal(a, b)
    })
  }

  private def equal(m1: VP, m2: VP): Boolean = {
    val u = OpenVariableReference(newUniqueId())
    // we use == here, because we don't deep compare a reduct
    equal(m1(u, NoFixReduction), m2(u, NoFixReduction))
  }

  // TODO this need to feed in reduction type
  private def equal(fs: AcyclicValuesGraph, gs: AcyclicValuesGraph): Boolean = {
    equalMv(fs.initials, gs.initials) && {
      val m = fs.initials.mapValues(_ => OpenVariableReference(newUniqueId()))
      m.isEmpty || equal(fs(m), gs(m))
    }
  }
  
  private def eqByAssump(a: Value, b: Value): Boolean = {
    if (a == b) {
      true
    } else if (assumptions.entryExists(a, _ == b)) {
      true
    } else {
      false
    }
  }

  private def guarded(a: Value, b: Value)(run: => Boolean): Boolean = {
    if (eqByAssump(a, b)) {
      true
    } else {
      if (a.isInstanceOf[RecursiveValue] && b.isInstanceOf[RecursiveValue])
      assumptions.addBinding(a, b)
      val res = run
      assumptions.removeBinding(a, b)
      res
    }
  }

  private def equal(a: Value, b: Value): Boolean = {
    guarded(a, b) {
      (a, b) match {
        case (ProjectionStuck(v1, s1), ProjectionStuck(v2, s2)) => s1 == s2 && equal(v1, v2)
        case (AppStuck(a1, v1), AppStuck(a2, v2)) => equal(a1, a2) && equal(v1, v2)
        case (FixApplication(a1, v1), FixApplication(a2, v2)) => equal(a1, a2) && equal(v1, v2)
        case (SplitStuck(s1, m1), SplitStuck(s2, m2)) => equal(s1, s2) && equalMvv(m1, m2)
        case (PiValue(d1, m1), PiValue(d2, m2)) => equal(d1, d2) && equal(m1, m2)
        case (LambdaValue(d1, m1), LambdaValue(d2, m2)) => equal(d1, d2) && equal(m1, m2)
        case (RecordValue(fs), RecordValue(gs)) => equal(fs, gs)
        case (MakeValue(fs), MakeValue(gs)) => equalMv(fs, gs)
        case (SumValue(ks, ts), SumValue(gs, js)) => ks == gs && ks.forall(k => equal(ts(k), js(k)))
        case (ConstructValue(n1, t1), ConstructValue(n2, t2)) => n1 == n2 && equal(t1, t2)
        case (_, _) => a == b
      }
    }
  }

  def equal(): Boolean = {
    return equal(a0, b0)
  }
}

object CompareValue {

  def equal(a: Value, b: Value) = new CompareValue(a, b).equal()
  def nonEmptyJoin(vs: Seq[Value]): Value = {
    assert(vs.tail.forall(a => equal(vs.head, a)), "The join is invalid, we currently only joins equal types")
    vs.head
  }
}