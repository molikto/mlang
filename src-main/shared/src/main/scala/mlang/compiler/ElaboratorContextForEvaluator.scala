package mlang.compiler

import mlang.compiler.Layer.Layers
import mlang.utils.Name

import scala.collection.mutable



trait ElaboratorContextForEvaluator extends EvaluatorContext  {
  protected def layers: Layers

  def getMetaReference(depth: Int, index: Int): Value.Meta = {

    layers(depth).metas(index)
  }

  // get value directly without resolving faces
  def getReference(depth: Int, index: Int): Value = layers(depth) match {
    case Layer.Parameter(binder, _) if index == -1 => binder.value
    case ps: Layer.Parameters  => ps.binders(index).value
    case Layer.Defines(_, terms) => terms(index).ref
    case _ => logicError()
  }


  def getDimension(depth: Int): Value.Formula = layers(depth).asInstanceOf[Layer.Dimension].value
}

