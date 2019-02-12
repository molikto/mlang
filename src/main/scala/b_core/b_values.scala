package b_core

import java.util.concurrent.atomic.AtomicLong


sealed trait Reduction {
  def next(): Boolean
}

case object FullReduction extends Reduction {
  override def next(): Boolean = true
}

case object NoReduction extends Reduction {
  override def next(): Boolean = false
}

case class OneReduction() extends Reduction {
  private var reduct: Boolean = false
  override def next(): Boolean = {
    if (reduct) {
      reduct = false
      true
    } else {
      false
    }
  }
}

object Value {

  def rebound(id: Long, in0: Value): VP = {
    VP((v, rd) => Value.rebound0(id, v, in0, rd))
  }

  private def rebound0(id: Long, by: Value, in0: Value, rd: Reduction): Value = {
    def rec(in: Value, rd: Reduction): Value = {
      in match {
        case OpenVariableReference(vi) => if (vi == id) by else in
        case OpenDeclarationReference(di, _) =>
          assert(di != id)
          in
        case ProjectionStuck(value, str) => rec(value, rd).projection(str)
        case AppStuck(atom, app) => rec(atom, rd).application(rec(app, rd))
        case SplitStuck(s, bs) => rec(s, rd).split(bs.mapValues(f => VP((a, rd) => rec(f(a), rd))))
        case ProjectionReduct(value, str) => ProjectionReduct(rec(value, rd).asInstanceOf[MakeValue], str)
        case AppReduct(atom, app) => AppReduct(rec(atom, rd).asInstanceOf[LambdaValue], rec(app, rd))
        case SplitReduct(s, bs) => SplitReduct(rec(s, rd).asInstanceOf[ConstructValue], bs.mapValues(f => VP((a, rd) => rec(f(a), rd))))
        case UniverseValue => in
        case PiValue(domain, map) => PiValue(rec(domain, rd), VP((a, rd) => rec(map(a), rd)))
        case LambdaValue(domain, map) => LambdaValue(rec(domain, rd), VP((a, rd) => rec(map(a), rd)))
        case RecordValue(fields) =>
          def recG(a: AcyclicValuesGraph): AcyclicValuesGraph = {
            AcyclicValuesGraph(a.initials.mapValues(a => rec(a, rd)), p => recG(a(p)))
          }
          RecordValue(recG(fields))
        case MakeValue(fields) => MakeValue(fields.mapValues(a => rec(a, rd)))
        case SumValue(keys, ts) => SumValue(keys, n => rec(ts(n), rd))
        case ConstructValue(name, term) => ConstructValue(name, rec(term, rd))
      }
    }
    rec(in0, rd)
  }

  private val uniqueIdGen =  new AtomicLong(0)

  def newUniqueId(): Long = uniqueIdGen.incrementAndGet()

}

/**
  *
  * to prevent infinite expansion of values, we wrap anything that can generate a value by a
  *
  */
case class VP(private val base: (Value, Reduction) => Value) {
  def apply(v: Value, reduct: Reduction = FullReduction): Value = {
    base(v, reduct)
  }
}

/**
  * if an object of this type == null then means this is the end
  */

object AcyclicValuesGraph {
  val empty = AcyclicValuesGraph(Map.empty, null)
  type Arg = Map[String, Value]
}
case class AcyclicValuesGraph(initials: Map[String, Value], private val base: AcyclicValuesGraph.Arg => AcyclicValuesGraph)
    extends (AcyclicValuesGraph.Arg => AcyclicValuesGraph) {

  import AcyclicValuesGraph._

  override def apply(v: Arg): AcyclicValuesGraph = {
    base(v)
  }
}


abstract sealed class Value {
  def application(v: Value, reductor: Reduction = FullReduction): Value  = throw new IllegalArgumentException("Not implemented")
  def projection(name: String, reductor: Reduction = FullReduction): Value = throw new IllegalArgumentException("Not implemented")
  def split(bs: Map[String, VP], reductor: Reduction = FullReduction): Value = throw new Exception()

  final override def hashCode(): Int = super.hashCode()
  final override def equals(obj: Any): Boolean = (this, obj) match {
    case (OpenVariableReference(i), OpenVariableReference(j)) => i == j
    case (OpenDeclarationReference(i, n), OpenDeclarationReference(j, m)) => i == j && n == m
    case (_, b) => super.equals(b)
  }
}


abstract sealed class StuckValue extends Value {
  override def application(seq: Value, reductor: Reduction): Value = AppStuck(this, seq)
  override def projection(s: String, reductor: Reduction) = ProjectionStuck(this, s)
  override def split(bs: Map[String, VP], reductor: Reduction) = SplitStuck(this, bs)
}

abstract sealed class ReductValue extends Value {

}

/**
  * open values is produced when you eval a term under a context where the value is absent
  */
case class OpenVariableReference(id: Long) extends StuckValue

case class OpenDeclarationReference(id: Long, name: String) extends StuckValue

case class ProjectionStuck(value: StuckValue, str: String) extends StuckValue
case class AppStuck(atom: StuckValue, app: Value) extends StuckValue
case class SplitStuck(s: StuckValue, names:  Map[String, VP]) extends StuckValue


case class ProjectionReduct(value: MakeValue, str: String) extends ReductValue
case class AppReduct(value: LambdaValue, app: Value) extends ReductValue
case class SplitReduct(s: ConstructValue, names:  Map[String, VP]) extends ReductValue

case object UniverseValue extends Value

case class PiValue(domain: Value, map: VP) extends Value

case class LambdaValue(domain: Value, map: VP) extends Value {
  override def application(v: Value, reductor: Reduction): Value =
    if (reductor.next()) map(v, reductor)
    else  AppReduct(this, v)

  def applicationOnce(v: Value): Value = map(v, OneReduction())
}


case class RecordValue(fields: AcyclicValuesGraph) extends Value

case class MakeValue(fields: Map[String, Value]) extends Value {
  override def projection(name: String, reductor: Reduction): Value =
    if (reductor.next()) fields(name)
    else ProjectionReduct(this, name)
}

// sum value is non-strict so it can have self-reference
case class SumValue(keys: Set[String], ts: String => Value) extends Value

case class ConstructValue(name: String, term: Value) extends Value {
  override def split(bs: Map[String, VP], reductor: Reduction): Value =
    if (reductor.next()) bs(name)(term, reductor)
    else SplitReduct(this, bs)

  def splitOnce(bs: Map[String, VP]): Value = bs(name)(term, OneReduction())
}
