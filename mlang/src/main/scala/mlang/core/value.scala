package mlang.core

import mlang.utils._

type Cofibration = Unit

object Telescope {
  type Values = Map[Unicode, Value]
  type Closure[T] = (Values, Reduction) => T

  case class Trunk[T](
    domain: Set[Unicode],
    body: Closure[T]
  )
}
import Telescope._

case class Telescope[T](
  initials: Map[Unicode, Value],
  trucks: Map[Unicode, Truck[Value]],
  terminal: Truck[T]
)


object Value {
  case class Constructor(name: Unicode, tele: Telescope[Unit]) // the int is the index
  enum Step {
    case Introduce(name: String, as: String)
  }
  case class Pattern(steps: Seq[Step], Closure[Value])
}


import Value._

// lambda (....) f(x,, fdfjsal)
// a.b, 

enum Value {
  case Universe(level: Int)

  case OpenReference(id: Long, annotation: Unicode) // hard stuck head
  // the evil **var** is to build up recursive data!!!
  case RecursiveReference(var to: Value, annotation: Unicode) // soft stuck head
  case SimpleReference(to: Value, annotation: Unicode) // soft stuck head

  case Pi(tele: Telescope[Value])
  case Lambda(patterns: Seq[Pattern])
  case Application(head: Value, argument: Telescope.Values) // spine, apply arguments to a stuck term
  // case PatternMachingStuck(value: Lambda, argument: SpineHeadPosition) //

  case Record(avg: Telescope[Unit])
  case Make(values: Telescope.Values)

  case Sum(constructors: Seq[Constructor])
  case Construct(name: Unicode, values: Telescope.Values)
  
  // TODO try to reduct more, in case some spine head position can use some reduction
  // def reductMoreOr(stuck: Value, recution: Reduction, success: Value => Value, fail: Value => Value): Value = {
  //   stuck match {
  //     case SimpleReference(to, _) => if (recution.reference >= 1) success(to) else fail(stuck)
  //     case RecursiveReference(to, _) => if (recution.reference >= 2) success(to) else fail(stuck)
  //     case _ => fail(stuck)
  //   }
  // }

  // def application(term: Value, reduction: Reduction = Reduction.Default): Value  = this match {
  //   case Lambda(application0) =>
  //     if (reduction.application) {
  //       application0(term, reduction)
  //     } else {
  //       Application(this, term)
  //     }
  //   case cl@CaseLambda(cases) =>
  //     if (reduction.application) {
  //       term match {
  //         case Construct(name, values) => 
  //           if (reduction.split) {
  //             cases.find(_.name == name).get.body(values, reduction)
  //           } else {
  //             CaseApplication(cl, term)
  //           }
  //         case _: StuckT => CaseApplication(cl, term)
  //         case _ => throw new IllegalArgumentException("Not possible")
  //       }
  //     } else {
  //       Application(this, term)
  //     }
  //   case _: StuckT =>
  //     reductMoreOr(this, reduction, s => s.application(term, reduction), s => Application(s, term))
  //   case _ => throw new IllegalArgumentException("Cannot perform application")
  // }
}