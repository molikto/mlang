package mlang.compiler

import mlang.compiler.ElaborationContext.Metas
import mlang.utils.Name


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
  val metas: Metas
}

object Layer {

  sealed trait Parameters extends Layer {
    def binders: Seq[ParameterBinder]
  }
  case class Parameter(binder: ParameterBinder, metas: Metas) extends Layer // lambda expression

  case class PatternParameters(binders: Seq[ParameterBinder], metas: Metas) extends Parameters

  case class ParameterGraph(defined: Seq[ParameterBinder], metas: Metas) extends Parameters {
    def binders: Seq[ParameterBinder] = defined
  }

  case class Defines(metas: Metas, terms: Seq[DefineItem]) extends Layer // notice the metas is FIRST!!
  case class Dimension(value: Value.Dimension.Generic, name: Name, metas: Metas) extends Layer {
    def id = value.id
  }
  case class Restriction(res: Value.Dimension, metas: Metas) extends Layer // no meta should be resolved here
}
