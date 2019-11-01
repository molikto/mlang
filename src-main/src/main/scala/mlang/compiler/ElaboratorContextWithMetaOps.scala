package mlang.compiler

import scala.collection.mutable


sealed trait ContextWithMetaOpsException extends CompilerException

object ContextWithMetaOpsException {
  case class MetaNotSolved() extends ContextWithMetaOpsException
}

object ElaboratorContextWithMetaOps {

  private val mgen = new GenLong.Positive()
}
import ElaboratorContextWithMetaOps._


trait ElaboratorContextWithMetaOps extends ElaboratorContextBase {

  def debug_metasSize = layers.head.metas.size

  protected def createMetas(): MetasState = new MetasState(mutable.ArrayBuffer.empty, 0)

  protected def solvedMeta(meta: Value.Meta): Abstract.MetaReference = {
    // TODO pretty print disabled this for now
    //assert(meta.isSolved)
    val ms = layers.head.metas
    if (ms.debug_final) logicError()
    val index = ms.size
    ms.append(meta)
    Abstract.MetaReference(0, index)
  }

  def clearMetas() = {
    val ms = layers.head.metas
    if (!ms.debug_allFrozen) logicError()
    if (ms.debug_final) logicError()
    ms.frozen = 0
    ms.metas.clear()
  }

  protected def newMeta(typ: Value): (Value.Meta, Abstract.MetaReference) = {
    val id = mgen()
    val v = Value.Meta(Value.MetaState.Open(id, typ))
    val ms = layers.head.metas
    if (ms.debug_final) logicError()
    val index = ms.size
    ms.append(v)
    (v, Abstract.MetaReference(0, index))
  }

  protected def rebindMeta(meta: Value.Meta): Abstract.MetaReference = {
    val ret = rebindMeta0(meta)
    if (ret == null) {
      logicError()
    }
    ret
  }


  protected def rebindMetaOpt(meta: Value.Meta): Option[Abstract.MetaReference] = {
    Option(rebindMeta0(meta))
  }

  protected def rebindOrAddMeta(meta: Value.Meta): Abstract.MetaReference = {
    val ret = rebindMeta0(meta)
    if (ret == null) solvedMeta(meta)
    else ret
  }

  private def rebindMeta0(meta: Value.Meta): Abstract.MetaReference = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.MetaReference = null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      var ll = ls.head.metas.metas
      while (ll.nonEmpty && binder == null) {
        ll.head._2.lookupChildren(meta) match {
          case Some(asgn) =>
            index = i
            binder = Abstract.MetaReference(up, index)
          case None =>
        }
        i += 1
        ll = ll.tail
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    binder
  }

  protected def finish(): Seq[Value.Meta] = {
    val ret = freeze()
    layers.head.metas.debug_final = true
    ret
  }

  protected def freeze(): Seq[Value.Meta] = {
    val vs = layers.head.metas.freeze()
    if (!vs.forall(_.isSolved)) throw ContextWithMetaOpsException.MetaNotSolved()
    vs
  }

}
