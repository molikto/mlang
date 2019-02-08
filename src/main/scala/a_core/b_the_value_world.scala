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

case class OpenAbstractionReference(index: Int) extends StuckValue

case class OpenDefinitionReference(index: Int, name: String) extends StuckValue

case class ProjectionStuck(value: StuckValue, str: String) extends StuckValue
case class AppStuck(atom: StuckValue, app: Value) extends StuckValue
case class SplitStuck(s: StuckValue, names:  Map[String, Value => Value]) extends StuckValue

case object UniverseValue extends Value

case class PiValue(domain: Value, map: Value => Value) extends Value

case class LambdaValue(domain: Value, map: Value => Value) extends Value


/**
  * if an object of this type == null then means this is the end
  */
object DependentValues {
  val empty = DependentValues(Map.empty, null)
}
case class DependentValues(independent: Map[String, Value], remaining: Map[String, Value] => DependentValues) {
}

case class RecordValue(fields: DependentValues) extends Value

case class MakeValue(fields: Map[String, Value]) extends Value

case class SumValue(ts: Map[String, Value]) extends Value

object Value {
  def abstractToValueMap(value: Value): Value => Value = ???
  def materializeToOpenReference(map: Value => Value): Value = ???
}

