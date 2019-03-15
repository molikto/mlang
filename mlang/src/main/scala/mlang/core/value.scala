package mlang.core

import mlang.utils._

type Cofibration = Unit

/**
the values is **typeless**
*/

object Value {

  type VP = (Value, Reduction) => Value // value map (with reduction)
  type VSP = (Seq[Value], Reduction) => Value // value sequence map (with reduction)
  type NVS = Map[Unicode, Value] // named values

  object AVG { // acylic value graph
    val empty = AVG(Map.empty, null)
  }
  case class AVG(initials: NVS, private val base: NVS => AVG) extends (NVS => AVG) {
    override def apply(v: NVS): AVG = {
      base(v)
    }
  }

  sealed trait StuckT // because of enum, we cannot say that all stuck is value anymore
  sealed trait StuckHeadT extends StuckT
  sealed trait HardStuckHeadT extends StuckHeadT
  sealed trait SoftStuckHeadT extends StuckHeadT
  sealed trait SpineT extends StuckT
  type SpineHeadPosition = Value // because we have All kinds of reduction methods

  case class Constructor(name: Unicode, pi: Pi)
  case class Case(name: Unicode, body: VSP)
}

import Value._



// cases of a value
// non-sutck
// hard_head
// spin - hard_head
// spin - soft_head  ==>  default when evaluating 

enum Value {
  case Universe(level: Int)

  case OpenReference(id: Long, annotation: Unicode) extends Value with HardStuckHeadT
  // the evil **var** is to build up recursive data!!!
  case RecursiveReference(var to: Value, annotation: Unicode) extends Value with SoftStuckHeadT
  case SimpleReference(to: Value, annotation: Unicode) extends Value with SoftStuckHeadT

  case Pi(domain: Value, codomain: VP)
  case Lambda(application0: VP)
  case CaseLambda(cases: Seq[Case])
  case Application(value: SpineHeadPosition, argument: Value) extends Value with SpineT

  case Record(avg: AVG)
  case Make(values: NVS)
  case Projection(value: SpineHeadPosition, field: Unicode) extends Value with SpineT

  case Sum(constructors: Seq[Constructor])
  case Construct(name: Unicode, values: Seq[Value])
  case CaseApplication(value: CaseLambda, argument: SpineHeadPosition) extends Value with SpineT
  
  def dereferenceOr(a: Value, recution: Reduction, success: Value => Value, fail: Value => Value): Value = {
    a match {
      case SimpleReference(to, _) => if (recution.reference >= 1) success(to) else fail(a)
      case RecursiveReference(to, _) => if (recution.reference >= 2) success(to) else fail(a)
      case _ => fail(a)
    }
  }

  def application(term: Value, reduction: Reduction = Reduction.Default): Value  = this match {
    case Lambda(application0) =>
      if (reduction.application) {
        application0(term, reduction)
      } else {
        Application(this, term)
      }
    case cl@CaseLambda(cases) =>
      if (reduction.application) {
        term match {
          case Construct(name, values) => 
            if (reduction.split) {
              cases.find(_.name == name).get.body(values, reduction)
            } else {
              CaseApplication(cl, term)
            }
          case _: StuckT => CaseApplication(cl, term)
          case _ => throw new IllegalArgumentException("Not possible")
        }
      } else {
        Application(this, term)
      }
    case _: StuckT =>
      dereferenceOr(this, reduction, s => s.application(term, reduction), s => Application(s, term))
    case _ => throw new IllegalArgumentException("Cannot perform application")
  }

  def projection(name: Unicode, reduction: Reduction = Reduction.Default): Value = this match {
    case Make(values) =>
      if (reduction.projection) {
        values(name)
      } else {
        Projection(this, name)
      }
    case _: StuckT =>
      dereferenceOr(this, reduction, s => s.projection(name, reduction), s => Projection(s, name))
    case _ => throw new IllegalArgumentException("Cannot perform projection")
  }
}