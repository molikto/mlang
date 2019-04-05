package mlang.core

import mlang.utils._




object Value {
  type VP = Value => Value
}

import Value._



enum Value {
  case Universe(level: Int)

  case OpenReference(id: Long, annotation: Unicode) // hard stuck head
  // the evil **var** is to build up recursive data!!!
  case RecursiveReference(var to: Value, annotation: Unicode) // soft stuck head
  case SimpleReference(to: Value, annotation: Unicode) // soft stuck head

  case Pi(domain: Value, codomain: VP)
  case Lambda(map: VP)
  case Application(head: Value, argument: Values) // spine, apply arguments to a stuck term

  case Record(avg: )
  case Make(values: )

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