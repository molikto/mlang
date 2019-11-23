package mlang.compiler

import mlang.compiler.Layer.Layers
import mlang.utils._
import mlang.compiler.semantic.Value
import mlang.compiler.semantic.given
import dbi.{Dependency, DependencyType}

import scala.collection.mutable



trait ElaboratorContextForEvaluator extends EvaluatorContext with ElaboratorContextBase  {

  def getMetaReference(depth: Int, index: Int, lvl: Int): Value = {
    if (lvl != 0) ???
    else getRestricted(layers(depth).metas(index), depth)
  }

  def getMetaReferenceType(depth: Int, index: Int, lvl: Int): Value = {
    if (lvl != 0) ???
    else getRestricted(layers(depth).metas.metas(index).typ, depth)
  }

  def getReferenceType(depth: Int, index: Int, lvl: Int): Value = getRestricted(layers(depth) match {
    case Layer.Parameter(binder, _) if index == -1 => binder.typ(evalHack, lvl)
    case ps: Layer.Parameters if index >= 0  => ps.termBinders(index).typ(evalHack, lvl)
    case Layer.Defines(_, terms) =>
      terms(index).typ(evalHack, lvl)
    case _ => logicError()
  }, depth)

  // get value directly without resolving faces
  def getReference(depth: Int, index: Int, lvl: Int): Value = getRestricted(layers(depth) match {
    case Layer.Parameter(binder, _) if index == -1 => binder.value.get(evalHack, lvl)
    case ps: Layer.Parameters if index >= 0  => ps.termBinders(index).value.get(evalHack, lvl)
    case Layer.Defines(_, terms) => terms(index).ref.get(evalHack, lvl)
    case _ => logicError()
  }, depth)

  def getDependency(d: Dependency): Object = {
    // println("getting dependency " + d)
    d.typ match {
      case DependencyType.Value => getReference(d.x, d.i, d.l)
      case DependencyType.Meta => getMetaReference(d.x, d.i, d.l)
      case DependencyType.Formula => getDimension(d.x, d.i)
    }
  }


  def getDimension(depth: Int, index: Int): semantic.Formula =
    getRestricted(layers(depth) match {
      case ps: Layer.Parameters if index >= 0 =>
        ps.dimensionBinders(index).value
      case d: Layer.Dimension if index == -1 =>
        d.binder.value
      case _ =>
        logicError()
    }, depth)
}

