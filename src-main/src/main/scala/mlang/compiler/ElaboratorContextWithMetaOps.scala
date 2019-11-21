package mlang.compiler

import scala.collection.mutable
import mlang.compiler.semantic.Value
import mlang.utils._
import mlang.compiler.dbi.Abstract
import mlang.compiler.dbi.given

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

  def evalHack(a: Abstract): Value = this.asInstanceOf[Evaluator].eval(a)

  protected def solveMeta(index: Int, body: Value, code: dbi.Abstract) = {
    val ms = layers.head.metas
    if (ms.debug_final) logicError()
    val mb = ms.metas(index)
    assert(!mb.value.isSolved)
    mb.value.state = semantic.MetaState.Closed(body)
    mb.value match {
      case g: Value.GlobalMeta =>
        g.lifter = (i: Int) => evalHack(code.lup(0, i))
      case _ =>
    }
    mb.code = code
  }

  protected def solvedMeta(meta: Value.Meta, typ: Value, code: dbi.Abstract): Abstract.MetaReference = {
    assert(meta.isSolved)
    val ms = layers.head.metas
    if (ms.debug_final) logicError()
    val index = ms.size
    ms.append(meta, typ, code)
    Abstract.MetaReference(0, index, 0)
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
    val v = Value.Meta(layers.size == 1, semantic.MetaState.Open(id, typ))
    val ms = layers.head.metas
    if (ms.debug_final) logicError()
    val index = ms.size
    ms.append(v, typ, null)
    (v, Abstract.MetaReference(0, index, 0))
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

  private def rebindMeta0(meta: Value.Meta): Abstract.MetaReference = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.MetaReference = null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      var ll = ls.head.metas.metas
      while (ll.nonEmpty && binder == null) {
        ll.head._2 match {
          case l: Value.LocalMeta =>
            l.lookupChildren(meta) match {
              case Some(asgn) =>
                index = i
                binder = Abstract.MetaReference(up, index, 0)
              case None =>
            }
          case g: Value.GlobalMeta =>
            g.lookupChildren(meta) match {
              case Some(l) => 
                index = i
                binder = Abstract.MetaReference(up, index, l)
              case None =>
            }
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

  protected def finish(): Seq[dbi.Abstract] = {
    val ret = freeze()
    layers.head.metas.debug_final = true
    ret
  }

  protected def freeze(): Seq[dbi.Abstract] = {
    val vs = layers.head.metas.freeze()
    vs
  }

}
