package mlang.compiler

import mlang.compiler.Layer.Layers
import mlang.compiler.semantic.Value
import mlang.compiler.semantic.given
import Value.{Referential}
import mlang.utils._

import scala.collection.mutable


case class MetaBinder(name: Name, value: Value.Meta, typ: Value, var code: dbi.Abstract /* is null when value is open */)

sealed trait Leveled[T <: Value] {
  val base: T
  def get(evl: Evaluator, i: Int): T
}

object Leveled {
  case class Fix[T <: Value](override val base: T) extends Leveled[T] {
    def get(evl: Evaluator, i: Int): T =
      if (i == 0) base
      else logicError()
  }
  class Floating[T <: Value](override val base: T, prepare: () => T, lifter: (Evaluator, Int) => Value, assgin: (a: T, a: Value) => Unit) extends Leveled[T] {
    private val cache = mutable.ArrayBuffer[T]()
    cache.append(base)
    def get(evl: Evaluator, i: Int): T = {
      while (cache.size <= i) {
        val a = prepare()
        cache.append(a)
        assgin(a, lifter(evl, cache.size - 1))
      }
      cache(i)
    }
    def all: Seq[T] = cache.toSeq
  }
}

class MetasState(val metas: mutable.ArrayBuffer[MetaBinder], var frozen: Int) {
  def debug_allFrozen: Boolean = metas.size == frozen

  def freeze(): Seq[dbi.Abstract] = {
    val vs = metas.slice(frozen, metas.size)
    if (!vs.forall(_.value.isSolved)) throw ContextWithMetaOpsException.MetaNotSolved()
    frozen = metas.size
    vs.map(_.code).toSeq
  }

  def freezeSize = frozen

  def apply(i: Int): Value.Meta = metas(i).value

  var debug_final = false
  def size: Int = metas.size

  def isEmpty: Boolean = metas.isEmpty
  def nonEmpty: Boolean = metas.nonEmpty
  def head: Value.Meta = metas.head.value

  def append(a: Value.Meta, typ: Value, code: dbi.Abstract): Unit = {
    if (debug_final) logicError()
    metas.append(MetaBinder(GenName(), a, typ, code))
  }
}

sealed trait Binder {
  def name: Name
}
case class ParameterBinder(name: Name, value: Leveled[Value.Generic]) extends Binder {
  def id: Long = value.base.id
  def typ(evl: Evaluator, lvl: Int): Value = value.get(evl, lvl).typ
  def baseType = typ(null, 0)
}

case class DimensionBinder(name: Name, value: semantic.Formula.Generic) extends Binder {
  def id: Long = value.id
}

// a defined term acts like a reference to parameter when it doesn't have a body
// the parameter will read back to the reference again
// so afterwards, we change the body of the reference and all is good silently
case class DefineItem(typ0: ParameterBinder, typCode: dbi.Abstract, ref: Leveled[Value.Reference], code: dbi.Abstract, isAxiom: Boolean = false) {
  def typ(evl: Evaluator, lvl: Int) = typ0.typ(evl, lvl)
  def baseType = typ(null, 0)
  def id: Long = typ0.id
  def name: Name = typ0.name
  def isDefined = ref.base.value != typ0.value.base
}

sealed trait Layer {
  val metas: MetasState
}

object Layer {
  type Layers = Seq[Layer]

  sealed trait Parameters extends Layer {

    def termBinders: Seq[ParameterBinder]
    def dimensionBinders: Seq[DimensionBinder]
    def binders: Seq[Binder]
    def typedIndex(index: Int): Int = {
      binders(index) match {
        case p: ParameterBinder => termBinders.indexWhere(_.id == p.id)
        case d: DimensionBinder => dimensionBinders.indexWhere(_.id == d.id)
      }
    }
  }
  case class Parameter(binder: ParameterBinder, metas: MetasState) extends Layer // lambda expression

  case class PatternParameters(
    binders: Seq[Binder],
    metas: MetasState
  ) extends Parameters {
    val termBinders = binders.filter(_.isInstanceOf[ParameterBinder]).map(_.asInstanceOf[ParameterBinder])
    val dimensionBinders = binders.filter(_.isInstanceOf[DimensionBinder]).map(_.asInstanceOf[DimensionBinder])
  }


  case class HitDefinition(self: Value, branches: Seq[AlternativeGraph])
  case class AlternativeGraph(name: Name, ims: Seq[Boolean], ps: semantic.ClosureGraph)

  case class ParameterGraph(
    hit: Option[HitDefinition],
    termBinders: Seq[ParameterBinder],
    dimensionBinders: Seq[DimensionBinder],
    metas: MetasState
  ) extends Parameters {
    val binders = termBinders ++ dimensionBinders
  }

  case class Defines(metas: MetasState, terms: Seq[DefineItem]) extends Layer // notice the metas is FIRST!!, for let expression and global
  case class Dimension(binder: DimensionBinder, metas: MetasState) extends Layer {
    def id = binder.id
  }

  // no meta should be resolved here
  case class Restriction(id: Long, res: semantic.Assignments, metas: MetasState) extends Layer
  case class ReifierRestriction(metas: MetasState) extends Layer
}


trait ElaboratorContextBase {
  protected def layers: Layers

  // FIXME remove this hack? how?
  def evalHack: Evaluator = this.asInstanceOf[Evaluator]

  protected def lookupMatched(ref: Leveled[Referential], a: Referential, up: Int): Option[Int] = {
    ref match {
      case fixed: Leveled.Fix[Referential] =>
        val l = fixed.base
        l.lookupChildren(a) match {
          case a@Some(asgs) =>
            if (getAllRestrictions(l.support().names, up) == asgs) Some(0)
            else logicError()
          case _ =>
            None
        }
      case floating: Leveled.Floating[Referential] =>
        val all = floating.all
        var res: Int = -1
        var i = 0
        while (i < all.size && res == -1) {
          val l = all(i)
          l.lookupChildren(a) match {
            case a@Some(asgs) =>
              if (getAllRestrictions(l.support().names, up) == asgs) res = i
              else logicError()
            case _ =>
          }
          i += 1
        }
        if (res == -1) None else Some(res)
    }
  }

  protected def getRestricted(v: Value, level: Int): Value = {
    val asg = getAllRestrictions(v.support().names, level)
    v.restrict(asg)
  }

  protected def getRestricted(v: semantic.Formula, level: Int): semantic.Formula = {
    val asg = getAllRestrictions(v.names, level)
    v.restrict(asg)
  }


  // these are just to be sure we got correct value out when reify
  @inline protected def getAllRestrictions(support: => Set[Long], level: Int): semantic.Assignments = {
    val rs = layers.take(level).flatMap {
      case r: Layer.Restriction =>
        r.res
      case _ => Set.empty
    }.toSet
    if (rs.isEmpty) {
      rs
    } else {
      val support0 = support
      val res = rs.filter(a => support0.contains(a._1))
      if (rs.nonEmpty) debug(s"geting restrictions returns $rs")
      res
    }
  }
}
