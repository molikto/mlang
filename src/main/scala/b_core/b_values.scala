package b_core

import java.util.concurrent.atomic.AtomicLong


sealed trait Reduction {
  def performFix(): Boolean
}

case object FullReduction extends Reduction {
  override def performFix(): Boolean = true
}

case object NoFixReduction extends Reduction {
  override def performFix(): Boolean = false
}


object Value {

  type VP = (Value, Reduction) => Value
  type VV = Value => Value

  def rebound(id: Long, in0: Value): VV = {
    (v) => Value.rebound0(id, v, in0)
  }

  private def rebound0(id: Long, by: Value, in0: Value): Value = {
    def rec(in: Value, rd: Reduction): Value = {
      in match {
        case OpenVariableReference(vi) => if (vi == id) by else in
        case OpenDeclarationReference(di, _) =>
          assert(di != id)
          in
        case ProjectionStuck(value, str) => rec(value, rd).projection(str)
        case AppStuck(atom, app) => rec(atom, rd).application(rec(app, rd))
        case FixApplication(atom, app) => rec(atom, rd).application(rec(app, rd))
        case SplitStuck(s, bs) => rec(s, rd).split(bs.mapValues(f => (a, rd) => rec(f(a, rd), rd)))
        case UniverseValue => in
        case PiValue(domain, map) => PiValue(rec(domain, rd), (a) => rec(map(a), rd))
        case LambdaValue(domain, map) => LambdaValue(rec(domain, rd), (a, rd) => rec(map(a, rd), rd))
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
    rec(in0, FullReduction)
  }

  private val uniqueIdGen =  new AtomicLong(0)

  def newUniqueId(): Long = uniqueIdGen.incrementAndGet()

}

trait RecursiveValue extends Value {
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

import Value._

abstract sealed class Value {
  def application(v: Value, reductor: Reduction = FullReduction): Value  = throw new IllegalArgumentException("Not implemented")
  def projection(name: String): Value = throw new IllegalArgumentException("Not implemented")
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
  override def projection(s: String) = ProjectionStuck(this, s)
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


/**
  * this stuck value only presents when your evaluation doesn't unfold fix
  */
case class FixApplication(lambda: LambdaValue, to: Value) extends StuckValue

case object UniverseValue extends Value

// NOTE the mapping inside Pi is not considered VP
case class PiValue(domain: Value, map: VV) extends Value {
}


case class LambdaValue(domain: Value, map: VP) extends Value {
  // beta and fix application
  override def application(v: Value, reductor: Reduction): Value =
    if (this.isInstanceOf[RecursiveValue] && !reductor.performFix()) {
      FixApplication(this, v)
    } else {
      map(v, reductor)
    }
}


case class RecordValue(fields: AcyclicValuesGraph) extends Value

case class MakeValue(fields: Map[String, Value]) extends Value {
  // NOTE is there a name for this??
  override def projection(name: String): Value = fields(name)
}

// sum value is non-strict so it can have self-reference
case class SumValue(keys: Set[String], ts: String => Value) extends RecursiveValue {

}

case class ConstructValue(name: String, term: Value) extends Value {
  // NOTE unlike iota, we perform the beta afterwards... consider make it better
  override def split(bs: Map[String, VP], reductor: Reduction): Value = bs(name)(term, reductor)
}
