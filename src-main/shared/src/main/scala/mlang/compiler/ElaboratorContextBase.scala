package mlang.compiler

import mlang.compiler.Layer.Layers
import mlang.utils.Name

import scala.collection.mutable


class MetasState(val metas: mutable.ArrayBuffer[Value.Meta], var frozen: Int) {
  def debug_allFrozen: Boolean = metas.size == frozen

  def freeze(): Seq[Value.Meta] = {
    val vs = metas.slice(frozen, metas.size)
    frozen = metas.size
    vs.toSeq
  }

  def apply(i: Int): Value.Meta = metas(i)

  var debug_final = false
  def size: Int = metas.size

  def isEmpty: Boolean = metas.isEmpty
  def nonEmpty: Boolean = metas.nonEmpty
  def head: Value.Meta = metas.head

  def append(a: Value.Meta): Unit = {
    if (debug_final) logicError()
    metas.append(a)
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

  case class PatternParameters(binders: Seq[ParameterBinder], metas: MetasState) extends Parameters

  case class ParameterGraph(defined: Seq[ParameterBinder], metas: MetasState) extends Parameters {
    def binders: Seq[ParameterBinder] = defined
  }

  case class Defines(metas: MetasState, terms: Seq[DefineItem]) extends Layer // notice the metas is FIRST!!
  case class Dimension(value: Value.Formula.Generic, name: Name, metas: MetasState) extends Layer {
    def id = value.id
  }

  // no meta should be resolved here
  case class Restriction(res: Value.Formula.Assignments, metas: MetasState) extends Layer

  case class ReifierRestriction(metas: MetasState) extends Layer
}


trait ElaboratorContextBase {
  protected def layers: Layers
}
