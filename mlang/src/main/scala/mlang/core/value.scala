package mlang.core

import mlang.utils._

type Cofibration = Unit

/**
value in weak head normal form (if given reduct = Default)
inductive definition will have recursive references as fields, this is ok
*/
object Value {

  type VP = (Value, Reduction) => Value // value map (with reduction)
  type VSP = (Seq[Value], Reduction) => Value // value sequence map (with reduction)
  type NVS = Map[Unicode, Value] // named values

  enum AVG[T, V] {
    case Terminal(v: V)
    case Cons(domain: Map[T, Value], map: (T => Value, Reduction) => AVG[T, V])

    def project(name: T, reduction: Reduction, access: T => Value): Value = this match {
      case Terminal(_) => throw new Exception("Tele cannot project on non-existing name")
      case Cons(ns, map) => ns.getOrElse(name, map(access, reduction).project(name, reduction, access))
    }
  }


  // because of enum, we cannot say that all stuck is value anymore, so we give them markers
  sealed trait StuckT
  sealed trait StuckHeadT extends StuckT
  sealed trait HardStuckHeadT extends StuckHeadT
  sealed trait SoftStuckHeadT extends StuckHeadT
  sealed trait SpineT extends StuckT
  type SpineHeadPosition = Value // because we have All kinds of reduction methods

  case class Constructor(name: Unicode, tele: AVG[Int, Unit]) // the int is the index
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

  case Record(avg: AVG[Unicode, Unit])
  case Make(values: NVS)
  case Projection(value: SpineHeadPosition, field: Unicode) extends Value with SpineT

  case Sum(constructors: Seq[Constructor])
  case Construct(name: Unicode, values: Seq[Value])
  case CaseApplication(value: CaseLambda, argument: SpineHeadPosition) extends Value with SpineT
  
  // TODO try to reduct more, in case some spine head position can use some reduction
  def reductMoreOr(stuck: Value, recution: Reduction, success: Value => Value, fail: Value => Value): Value = {
    stuck match {
      case SimpleReference(to, _) => if (recution.reference >= 1) success(to) else fail(stuck)
      case RecursiveReference(to, _) => if (recution.reference >= 2) success(to) else fail(stuck)
      case _ => fail(stuck)
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
      reductMoreOr(this, reduction, s => s.application(term, reduction), s => Application(s, term))
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
      reductMoreOr(this, reduction, s => s.projection(name, reduction), s => Projection(s, name))
    case _ => throw new IllegalArgumentException("Cannot perform projection")
  }
}