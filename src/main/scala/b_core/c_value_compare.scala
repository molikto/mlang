package b_core

import b_core.Value.ValueMap


/**
  * a value compare class that handles recursive values
  */
class CompareValue(a0: Value, b0: Value) {

  import Value.newUniqueId

  private def equalMvv(m1: Map[String, ValueMap], m2: Map[String, ValueMap]): Boolean = {
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

  private def equal(m1: ValueMap, m2: ValueMap): Boolean = {
    // TODO mmm... I need to reconsider this...
    m1.eq(m2) || {
      val u = OpenVariableReference(newUniqueId())
      equal(m1(u), m2(u))
    }
  }

  private def equal(fs: AcyclicValuesGraph, gs: AcyclicValuesGraph): Boolean = {
    equalMv(fs.initials, gs.initials) && {
      val m = fs.initials.mapValues(_ => OpenVariableReference(newUniqueId()))
      m.isEmpty || equal(fs.remaining(m), gs.remaining(m))
    }
  }

  private def equal(a: Value, b: Value, firstCheck: Boolean = false): Boolean = {
    if (a.eq(b)) {
      true
    } else if (!firstCheck && a.eq(a0) && b.eq(b0)) {
      true
    } else {
      (a, b) match {
        case (ProjectionStuck(v1, s1), ProjectionStuck(v2, s2)) => s1 == s2 && equal(v1, v2)
        case (AppStuck(a1, v1), AppStuck(a2, v2)) => equal(a1, a2) && equal(v1, v2)
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
    return equal(a0, b0, firstCheck = true)
  }
}

object CompareValue {

  def equal(a: Value, b: Value) = new CompareValue(a, b).equal()
  def nonEmptyJoin(vs: Seq[Value]): Value = {
    assert(vs.tail.forall(a => equal(vs.head, a)), "The join is invalid, we currently only joins equal types")
    vs.head
  }
}