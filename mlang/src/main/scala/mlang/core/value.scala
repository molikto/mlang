package mlang.core

import mlang.utils._

type Cofibration = Unit

/**
the values is **typeless**
*/
case class Reduction(
  application: Boolean,
  split: Boolean,
  projection: Boolean,
  reference: Boolean)

object Reduction {
  // notice we DON'T expand recursive references!!!
  //
  // but --
  // a soft stuck is a closed recursive reference
  // the default reduction will ensure outermost is NOT a soft stuck
  // but it might be in other places, like in a sum type, the branches
  val Default = Reduction(true, true, true, true)
}

sealed trait Value {
  def application(v: Value, reductor: Reduction = Reduction.Default): Value  = throw new IllegalArgumentException("Not implemented")
  def projection(name: Unicode, reduction: Reduction = Reduction.Default): Value = throw new IllegalArgumentException("Not implemented")
}




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

  sealed trait Stuck extends Value {
    override def application(term: Value, reduction: Reduction) = LambdaApplication(this, term) // should here save the reduction values?
    override def projection(name: Unicode, r: Reduction) = Projection(this, name)
  }

  type Head = Value // because we have All kinds of reduction methods

// cases of a value
// non-sutck
// hard_head
// spin - hard_head
// spin - soft_head  ==>  default when evaluating 

  sealed trait StuckHead extends Stuck
  sealed trait Spine extends Stuck

  case class Universe(level: Int) extends Value {
  }

  case class OpenReference(id: Long, annotation: Unicode) extends StuckHead

  // the evil **var** is to build up recursive data!!!
  case class ClosedRecursiveReference(var to: Value, annotation: Unicode) extends StuckHead

  case class ClosedReference(to: Value, annotation: Unicode) extends Value


  case class Pi(domain: Value, codomain: VP) extends Value

  case class Lambda(application0: VP) extends Value {
    override def application(term: Value, reduction: Reduction) = {
      if (reduction.application) {
        application0(term, reduction)
      } else {
        LambdaApplication(this, term)
      }
    }
  }


  case class LambdaApplication(value: Head, argument: Value) extends Spine
  case class Record(avg: AVG) extends Value

  case class Make(values: NVS) extends Value {
    override def projection(name: Unicode, reduction: Reduction) = {
      if (reduction.projection) {
        values(name)
      } else {
        Projection(this, name)
      }
    }
  }

  case class Projection(value: Head, field: Unicode) extends Spine

  case class Constructor(name: Unicode, pi: Pi)
  case class Sum(constructors: Seq[Constructor]) extends Value {
    val names = constructors.map(_.name).toSet
  }

  case class Construct(name: Unicode, values: Seq[Value]) extends Value
}