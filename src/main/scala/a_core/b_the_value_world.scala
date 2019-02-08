package a_core


abstract sealed class Value {
  def application(v: Value): Value  = throw new IllegalArgumentException("Not implemented")
  def projection(name: String): Value = throw new IllegalArgumentException("Not implemented")
  def split(bs: Map[String, Value => Value]): Value = throw new Exception()
}

abstract sealed class StuckValue extends Value {
  override def application(seq: Value): Value = AppStuck(this, seq)
  override def projection(s: String) = ProjectionStuck(this, s)
  override def split(bs: Map[String, Value => Value]) = SplitStuck(this, bs)
}

/**
  * open values is produced when you eval a term under a context where the value is absent
  */
case class OpenVariableReference(id: Long) extends StuckValue

case class OpenDeclarationReference(id: Long, name: String) extends StuckValue

case class ProjectionStuck(value: StuckValue, str: String) extends StuckValue
case class AppStuck(atom: StuckValue, app: Value) extends StuckValue
case class SplitStuck(s: StuckValue, names:  Map[String, Value => Value]) extends StuckValue

case object UniverseValue extends Value

case class PiValue(domain: Value, map: Value => Value) extends Value

case class LambdaValue(domain: Value, map: Value => Value) extends Value

/**
  * if an object of this type == null then means this is the end
  */
object AcyclicValuesGraph {
  val empty = AcyclicValuesGraph(Map.empty, null)
}
case class AcyclicValuesGraph(initials: Map[String, Value], remaining: Map[String, Value] => AcyclicValuesGraph) {
}

case class RecordValue(fields: AcyclicValuesGraph) extends Value

case class MakeValue(fields: Map[String, Value]) extends Value

case class SumValue(ts: Map[String, Value]) extends Value

case class ConstructValue(name: String, term: Value) extends Value

object Value {

  def replacingVariableValue(id: Long, by: Value, in0: Value): Value = {
    def rec(in: Value): Value = {
      in match {
        case OpenVariableReference(vi) => if (vi == id) by else in
        case OpenDeclarationReference(di, name) =>
          assert(di != id)
          in
        case ProjectionStuck(value, str) => rec(value).projection(str)
        case AppStuck(atom, app) => rec(atom).application(rec(app))
        case SplitStuck(s, names) => rec(s).split(names.mapValues(f => (a => rec(f(a)))))
        case UniverseValue => in
        case PiValue(domain, map) => PiValue(rec(domain), a => rec(map(a)))
        case LambdaValue(domain, map) => LambdaValue(rec(domain), a => rec(map(a)))
        case RecordValue(fields) =>
          def recG(a: AcyclicValuesGraph): AcyclicValuesGraph = {
            AcyclicValuesGraph(a.initials.mapValues(rec), p => recG(a.remaining(p)))
          }
          RecordValue(recG(fields))
        case MakeValue(fields) => MakeValue(fields.mapValues(rec))
        case SumValue(ts) => SumValue(ts.mapValues(rec))
        case ConstructValue(name, term) => ConstructValue(name, rec(term))
      }
    }
    rec(in0)
  }
}
