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

case class ParameterBinder(name: Name, value: Value.Generic) {
  def id: Long = value.id
  def typ: Value = value.typ
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
    def binders: Seq[ParameterBinder]
  }
  case class Parameter(binder: ParameterBinder, metas: MetasState) extends Layer // lambda expression

  case class PatternParameters(binders: Seq[ParameterBinder], metas: MetasState) extends Parameters // for pattern matching

  case class HitDefinition(self: Value, branches: Seq[AlternativeGraph])
  case class AlternativeGraph(name: Name, ps: Value.ClosureGraph, dim: Int)

  case class ParameterGraph(
    hit: Option[HitDefinition],
    defined: Seq[ParameterBinder],
    metas: MetasState
  ) extends Parameters { // for pi and record telescope
    def binders: Seq[ParameterBinder] = defined
  }

  case class Defines(metas: MetasState, terms: Seq[DefineItem]) extends Layer // notice the metas is FIRST!!, for let expression and global
  case class Dimension(value: Value.Formula.Generic, name: Name, metas: MetasState) extends Layer {
    def id = value.id
  }

  // no meta should be resolved here
  case class Restriction(id: Long, res: Value.Formula.Assignments, metas: MetasState) extends Layer
  case class ReifierRestriction(metas: MetasState) extends Layer
}


trait ElaboratorContextBase {
  protected def layers: Layers



  protected def restrictionsMatchWith(up: Int, asgns: Value.Formula.Assignments) = {
    getAllRestrictions(up) == asgns
  }

  protected def lookupMatched(ref: Referential, a: Referential, up: Int) = {
    ref.lookupChildren(a) match {
      case a@Some(asgs) if restrictionsMatchWith(up, asgs) =>
        a
      case _ =>
        None
    }
  }

  protected def getAllRestrictions(level: Int): Value.Formula.Assignments = {
    val ids = layers.drop(level).flatMap {
      case d: Layer.Dimension => Seq(d.value.id)
      case _ => Seq.empty
    }
    if (ids.isEmpty) {
      Set.empty
    } else {
      val rs = layers.take(level).flatMap {
        case r: Layer.Restriction =>
          r.res.filter(a => ids.contains(a._1))
        case _ => Set.empty[Value.Formula.Assignment]
      }.toSet
      debug(s"geting restrictions returns $rs")
      rs
    }
  }
}
