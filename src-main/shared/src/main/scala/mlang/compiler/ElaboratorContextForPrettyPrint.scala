package mlang.compiler


trait ElaboratorContextForPrettyPrint extends EvaluatorContext with ElaboratorContextBase  {

  def getMetaReference(depth: Int, index: Int): Value = {
    layers(depth).metas(index).restrict(getAllRestrictions(depth))
  }

  // get value directly without resolving faces
  def getReference(depth: Int, index: Int): Value = (layers(depth) match {
    case Layer.Parameter(binder, _) if index == -1 => binder.value
    case ps: Layer.Parameters  => ps.binders(index).value
    case Layer.Defines(_, terms) => terms(index).ref
    case _ => logicError()
  }).restrict(getAllRestrictions(depth))


  def getDimension(depth: Int): Value.Formula =
    layers(depth).asInstanceOf[Layer.Dimension].value.restrict(getAllRestrictions(depth))
}

