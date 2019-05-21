package mlang.core

import mlang.core.Context.Metas

import scala.collection.mutable


sealed trait ContextWithMetaOpsException extends CoreException

object ContextWithMetaOpsException {

  case class MetaNotSolved() extends ContextWithMetaOpsException
}

object ContextWithMetaOps {

  private val mgen = new LongGen.Positive()
}
import ContextWithMetaOps._


trait ContextWithMetaOps extends Context {

  def debug_metasSize = layers.head.metas.size

  protected def createMetas(): Metas = new Metas(mutable.ArrayBuffer.empty, 0)

  protected def solvedMeta(meta: Value.Meta): Abstract.MetaReference = {
    assert(meta.isSolved)
    val ms = layers.head.metas
    if (ms.debug_final) logicError()
    val index = ms.size
    ms.append(meta)
    Abstract.MetaReference(0, index)
  }

  protected def newMeta(typ: Value): Abstract.MetaReference = {
    val id = mgen()
    val v = Value.Meta(Value.Meta.Open(id, typ))
    val ms = layers.head.metas
    if (ms.debug_final) logicError()
    val index = ms.size
    ms.append(v)
    Abstract.MetaReference(0, index)
  }

  protected def rebindMeta(meta: Value.Meta): Abstract.MetaReference = {
    rebindOrAddMeta0(meta, false)
  }

  protected def rebindOrAddMeta(meta: Value.Meta): Abstract.MetaReference = {
    rebindOrAddMeta0(meta, true)
  }

  private def rebindOrAddMeta0(meta: Value.Meta, allowAdd: Boolean): Abstract.MetaReference = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.MetaReference = null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      var ll = ls.head.metas.metas
      while (ll.nonEmpty && binder == null) {
        if (ll.head.eq(meta)) {
          index = i
          binder = Abstract.MetaReference(up, index)
        }
        i += 1
        ll = ll.tail
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    if (binder == null) {
      if (allowAdd) {
        solvedMeta(meta)
      } else {
        logicError()
      }
    } else {
      binder
    }
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
