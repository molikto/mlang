package mlang.compiler

import mlang.compiler.Layer.{Layers, Restriction}
import mlang.utils.{Name, debug}

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


  def getDimension(depth: Int): Value.Formula = {
    val asgs = layers.take(depth).flatMap {
      case r: Layer.Restriction => r.res
      case _: Layer.ReifierRestriction => logicError()
      case _ => None
    }.toSet
    if (debug.enabled) assert(Value.Formula.satisfiable(asgs))
    layers(depth).asInstanceOf[Layer.Dimension].value.simplify(asgs)
  }
}

