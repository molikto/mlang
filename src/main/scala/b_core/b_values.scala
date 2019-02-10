package b_core

import java.util.concurrent.atomic.AtomicLong



object Value {

  def rebound(id: Long, by: Value, in0: Value): Value = {
    def rec(in: Value): Value = {
      in match {
        case OpenVariableReference(vi) => if (vi == id) by else in
        case OpenDeclarationReference(di, _) =>
          assert(di != id)
          in
        case ProjectionStuck(value, str) => rec(value).projection(str)
        case AppStuck(atom, app) => rec(atom).application(rec(app))
        case SplitStuck(s, bs) => rec(s).split(bs.mapValues(f => a => rec(f(a))))
        case UniverseValue => in
        case PiValue(domain, map) => PiValue(rec(domain), a => rec(map(a)))
        case LambdaValue(domain, map) => LambdaValue(rec(domain), a => rec(map(a)))
        case RecordValue(fields) =>
          def recG(a: AcyclicValuesGraph): AcyclicValuesGraph = {
            AcyclicValuesGraph(a.initials.mapValues(rec), p => recG(a.remaining(p)))
          }
          RecordValue(recG(fields))
        case MakeValue(fields) => MakeValue(fields.mapValues(rec))
        case SumValue(keys, ts) => SumValue(keys, n => rec(ts(n)))
        case ConstructValue(name, term) => ConstructValue(name, rec(term))
      }
    }
    rec(in0)
  }

  private val uniqueIdGen =  new AtomicLong(0)

  def newUniqueId(): Long = uniqueIdGen.incrementAndGet()

  type ValueMap = Value => Value
}

import Value._

abstract sealed class Value {
  def application(v: Value): Value  = throw new IllegalArgumentException("Not implemented")
  def projection(name: String): Value = throw new IllegalArgumentException("Not implemented")
  def split(bs: Map[String, ValueMap]): Value = throw new Exception()
}


abstract sealed class StuckValue extends Value {
  override def application(seq: Value): Value = AppStuck(this, seq)
  override def projection(s: String) = ProjectionStuck(this, s)
  override def split(bs: Map[String, ValueMap]) = SplitStuck(this, bs)
}

/**
  * open values is produced when you eval a term under a context where the value is absent
  */
case class OpenVariableReference(id: Long) extends StuckValue

case class OpenDeclarationReference(id: Long, name: String) extends StuckValue

case class ProjectionStuck(value: StuckValue, str: String) extends StuckValue
case class AppStuck(atom: StuckValue, app: Value) extends StuckValue
case class SplitStuck(s: StuckValue, names:  Map[String, ValueMap]) extends StuckValue

case object UniverseValue extends Value

case class PiValue(domain: Value, map: ValueMap) extends Value

case class LambdaValue(domain: Value, map: ValueMap) extends Value {
  override def application(v: Value): Value = map(v)
}

/**
  * if an object of this type == null then means this is the end
  */

object AcyclicValuesGraph {
  val empty = AcyclicValuesGraph(Map.empty, null)
}
case class AcyclicValuesGraph(initials: Map[String, Value], remaining: Map[String, Value] => AcyclicValuesGraph) {
}

case class RecordValue(fields: AcyclicValuesGraph) extends Value

case class MakeValue(fields: Map[String, Value]) extends Value {
  override def projection(name: String): Value = fields(name)
}

// sum value is non-strict so it can have self-reference
case class SumValue(keys: Set[String], ts: String => Value) extends Value

case class ConstructValue(name: String, term: Value) extends Value {
  override def split(bs: Map[String, ValueMap]): Value = bs(name)(term)
}
