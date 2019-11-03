package mlang.compiler.semantic



trait ObjWorker {
  def supportShallow(func: AnyRef): SupportShallow

  def restrict(a: AnyRef, b: Assignments): AnyRef
}


var RESTRICT_OBJ: ObjWorker = null