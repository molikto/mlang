package mlang.compiler

import mlang.compiler.Layer.Layers
import mlang.utils.Name

import scala.collection.mutable



trait ElaboratorContextForEvaluator extends EvaluatorContext with ElaboratorContextBase  {

  def getMetaReference(depth: Int, index: Int): Value = {
    getRestricted(layers(depth).metas(index), depth)
  }

  def getMetaReferenceType(depth: Int, index: Int): Value = {
    getRestricted(layers(depth).metas(index), depth)
  }

  def getReferenceType(depth: Int, index: Int): Value = getRestricted(layers(depth) match {
    case Layer.Parameter(binder, _) if index == -1 => binder.typ
    case ps: Layer.Parameters if index >= 0  => ps.termBinders(index).typ
    case Layer.Defines(_, terms) => terms(index).typ
    case _ => logicError()
  }, depth)

  // get value directly without resolving faces
  def getReference(depth: Int, index: Int): Value = getRestricted(layers(depth) match {
    case Layer.Parameter(binder, _) if index == -1 => binder.value
    case ps: Layer.Parameters if index >= 0  => ps.termBinders(index).value
    case Layer.Defines(_, terms) => terms(index).ref
    case _ => logicError()
  }, depth)


  def getDimension(depth: Int, index: Int): Value.Formula =
    getRestricted(layers(depth) match {
      case ps: Layer.Parameters if index >= 0 =>
        ps.dimensionBinders(index).value
      case d: Layer.Dimension if index == -1 =>
        d.binder.value
      case _ =>
        logicError()
    }, depth)
}

