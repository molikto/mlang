package b_core

import java.util.concurrent.atomic.AtomicLong

import scala.collection.mutable


object Value {

  def rebound(id: Long, in0: Value): VP = {
    VP((v, rd) => Value.rebound0(id, v, in0, rd))
  }

  private def rebound0(id: Long, by: Value, in0: Value, rd: Boolean): Value = {
    def rec(in: Value, rd: Boolean): Value = {
      in match {
        case OpenVariableReference(vi) => if (vi == id) by else in
        case OpenDeclarationReference(di, _) =>
          assert(di != id)
          in
        case ProjectionStuck(value, str) => rec(value, rd).projection(str)
        case AppStuck(atom, app) => rec(atom, rd).application(rec(app, rd))
        case SplitStuck(s, bs) => rec(s, rd).split(bs.mapValues(f => VP((a, rd) => rec(f(a), rd))))
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
case class VP(private val base: (Value, Boolean) => Value) {
  def apply(v: Value, reduct: Boolean = false): Value = {
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

  val cache = mutable.Map.empty[Arg, AcyclicValuesGraph]
  override def apply(v: Arg): AcyclicValuesGraph = {
    cache.get(v) match {
      case Some(a) => a
      case None =>
        val n = base(v)
        cache.put(v, n)
        n
    }
  }
}


abstract sealed class Value {
  def application(v: Value, reductor: Boolean = false): Value  = throw new IllegalArgumentException("Not implemented")
  def projection(name: String, reductor: Boolean = false): Value = throw new IllegalArgumentException("Not implemented")
  def split(bs: Map[String, VP], reductor: Boolean = false): Value = throw new Exception()

  final override def hashCode(): Int = super.hashCode()
  final override def equals(obj: Any): Boolean = super.equals(obj)
}


abstract sealed class StuckValue extends Value {
  override def application(seq: Value, reductor: Boolean): Value = AppStuck(this, seq)
  override def projection(s: String, reductor: Boolean) = ProjectionStuck(this, s)
  override def split(bs: Map[String, VP], reductor: Boolean) = SplitStuck(this, bs)
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
  override def application(v: Value, reductor: Boolean): Value =
    if (reductor) AppReduct(this, v)
    else map(v, reductor)

  def applicationOnce(v: Value): Value = map(v, true)
}


case class RecordValue(fields: AcyclicValuesGraph) extends Value

case class MakeValue(fields: Map[String, Value]) extends Value {
  override def projection(name: String, reductor: Boolean): Value =
    if (reductor) ProjectionReduct(this, name)
    else fields(name)
}

// sum value is non-strict so it can have self-reference
case class SumValue(keys: Set[String], ts: String => Value) extends Value

case class ConstructValue(name: String, term: Value) extends Value {
  override def split(bs: Map[String, VP], reductor: Boolean): Value =
    if (reductor) SplitReduct(this, bs)
    else bs(name)(term, reductor)

  def splitOnce(bs: Map[String, VP]): Value = bs(name)(term, true)
}
