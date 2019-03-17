package mlang.core

import mlang.utils._

type Cofibration = Unit


type IndexedValues[K] = Map[K, Value]

type ValueMap[K, T] = (IndexedValues[K], Reduction) => T

case class Trunk[K, T](
  domain: Set[K],
  body: ValueMap[K, T]
)

case class ValueGraph[K, T](
  initials: IndexedValues[K], // unknown values of known type's name => type
  trucks: Map[K, Trunk[K, Value]],  // values depends on un unknown values
  termial: Trunk[K, T]
)

/**
value in weak head normal form (if given reduct = Default)
inductive definition will have recursive references as fields, this is ok
*/
object Value {
  case class Constructor(name: Unicode, tele: ValueGraph[Int, Unit]) // the int is the index
}

import Value._



// cases of a value
// non-sutck
// hard_head
// spin - hard_head
// spin - soft_head  ==>  default when evaluating 

enum Value {
  case Universe(level: Int)

  case OpenReference(id: Long, annotation: Unicode) // hard stuck head
  // the evil **var** is to build up recursive data!!!
  case RecursiveReference(var to: Value, annotation: Unicode) // soft stuck head
  case SimpleReference(to: Value, annotation: Unicode) // soft stuck head

  case Pi(graph: ValueGraph[Int, Value])
  case Lambda(pattern: ValueMap[Int, Value])
  case Application(head: Value, argument: IndexedValues[Int]) // spine, apply arguments to a stuck term
  // case PatternMachingStuck(value: Lambda, argument: SpineHeadPosition) //

  case Record(avg: ValueGraph[Unicode, Unit])
  case Make(values: IndexedValues[Unicode])

  case Sum(constructors: Seq[Constructor])
  case Construct(name: Unicode, values: IndexedValues[Int])
  
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