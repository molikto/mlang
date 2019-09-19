package mlang.compiler

import mlang.compiler.Layer.Layers
import mlang.compiler.Value.{Referential}
import mlang.utils.{Name, debug}

import scala.collection.mutable


class MetasState(val metas: mutable.ArrayBuffer[(Name, Value.Meta)], var frozen: Int) {
  def debug_allFrozen: Boolean = metas.size == frozen

  def freeze(): Seq[Value.Meta] = {
    val vs = metas.slice(frozen, metas.size)
    frozen = metas.size
    vs.map(_._2).toSeq
  }

  def apply(i: Int): Value.Meta = metas(i)._2

  var debug_final = false
  def size: Int = metas.size

  def isEmpty: Boolean = metas.isEmpty
  def nonEmpty: Boolean = metas.nonEmpty
  def head: Value.Meta = metas.head._2

  def append(a: Value.Meta): Unit = {
    if (debug_final) logicError()
    metas.append((GenName(), a))
  }
}

sealed trait Binder {
  def name: Name
}
case class ParameterBinder(name: Name, value: Value.Generic) extends Binder {
  def id: Long = value.id
  def typ: Value= value.typ
}

case class DimensionBinder(name: Name, value: Value.Formula.Generic) extends Binder {
  def id: Long = value.id
}

// a defined term acts like a parameter when it doesn't have a body
case class DefineItem(typ0: ParameterBinder, ref0: Option[Value.Reference]) {
  def typ: Value = typ0.value.typ
  def id: Long = typ0.id
  def name: Name = typ0.name
  def isDefined = ref0.isDefined
  def ref = ref0.getOrElse(typ0.value)
}

sealed trait Layer {
  val metas: MetasState
}

object Layer {
  type Layers = Seq[Layer]

  sealed trait Parameters extends Layer {

    def termBinders: Seq[ParameterBinder]
    def dimensionBinders: Seq[DimensionBinder]
    def binders: Seq[Binder]
    def typedIndex(index: Int): Int = {
      binders(index) match {
        case p: ParameterBinder => termBinders.indexWhere(_.id == p.id)
        case d: DimensionBinder => dimensionBinders.indexWhere(_.id == d.id)
      }
    }
  }
  case class Parameter(binder: ParameterBinder, metas: MetasState) extends Layer // lambda expression

  case class PatternParameters(
    binders: Seq[Binder],
    metas: MetasState
  ) extends Parameters {
    val termBinders = binders.filter(_.isInstanceOf[ParameterBinder]).map(_.asInstanceOf[ParameterBinder])
    val dimensionBinders = binders.filter(_.isInstanceOf[DimensionBinder]).map(_.asInstanceOf[DimensionBinder])
  }


  case class HitDefinition(self: Value, branches: Seq[AlternativeGraph])
  case class AlternativeGraph(name: Name, ps: Value.ClosureGraph)

  case class ParameterGraph(
    hit: Option[HitDefinition],
    termBinders: Seq[ParameterBinder],
    dimensionBinders: Seq[DimensionBinder],
    metas: MetasState
  ) extends Parameters {
    val binders = termBinders ++ dimensionBinders
  }

  case class Defines(metas: MetasState, terms: Seq[DefineItem]) extends Layer // notice the metas is FIRST!!, for let expression and global
  case class Dimension(binder: DimensionBinder, metas: MetasState) extends Layer {
    def id = binder.id
  }

  // no meta should be resolved here
  case class Restriction(id: Long, res: Value.Formula.Assignments, metas: MetasState) extends Layer
  case class ReifierRestriction(metas: MetasState) extends Layer
}


trait ElaboratorContextBase {
  protected def layers: Layers

  protected def lookupMatched(ref: Referential, a: Referential, up: Int) = {
    ref.lookupChildren(a) match {
      case a@Some(asgs) if getAllRestrictions(ref.support().names, up) == asgs =>
        a
      case _ =>
        None
    }
  }

  protected def getRestricted(v: Value, level: Int): Value = {
    val asg = getAllRestrictions(v.support().names, level)
    v.restrict(asg)
  }

  protected def getRestricted(v: Value.Formula, level: Int): Value.Formula = {
    val asg = getAllRestrictions(v.names, level)
    v.restrict(asg)
  }

  // these are just to be sure we got correct value out when reify
  @inline protected def getAllRestrictions(support: => Set[Long], level: Int): Value.Formula.Assignments = {
    val rs = layers.take(level).flatMap {
      case r: Layer.Restriction =>
        r.res
      case _ => Set.empty[Value.Formula.Assignment]
    }.toSet
    if (rs.isEmpty) {
      rs
    } else {
      val support0 = support
      val res = rs.filter(a => support0.contains(a._1))
      if (rs.nonEmpty) debug(s"geting restrictions returns $rs")
      res
    }
  }
}
