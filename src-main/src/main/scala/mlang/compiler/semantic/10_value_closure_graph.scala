package mlang.compiler.semantic

import mlang.utils._
import mlang.compiler.GenLong.Negative.{dgen, gen}
import Value.{Meta, Generic}
import scala.collection.mutable

trait ClosureGraph {
  def apply(i: Int) = graph(i)
  def graph: Seq[ClosureGraph.Node]
  def size : Int = graph.size
  def isEmpty: Boolean = size == 0

  def dimSize: Int
  def restrictions(): System[ValueClosure] // only in a fully reduced
  def phi(): Set[Formula]

  def reduce(ds: Seq[Formula]): ClosureGraph
  def reduceAll(vs: Seq[Value]): ClosureGraph = {
    assert(vs.size == graph.size)
    vs.zipWithIndex.foldLeft(this) { (g, v) => g.reduce(v._2, v._1) }
  }
  def reduce(i: Int, a: Value): ClosureGraph
  def get(name: Int, values: Int => Value): Value
}

export ClosureGraph.isNominal


case class ClosureGraphArguments(dependencies: Seq[Int], metaCount: Int, map: (Seq[Value], Seq[Value]) => (Seq[Meta], Value))

object ClosureGraph {


  val empty: ClosureGraph = Impl(Seq.empty, 0, RestrictionsState.empty)

  sealed trait Node {
    def dependencies: Seq[Int]
    def independent: Independent = this.asInstanceOf[Independent]
  }

  sealed trait Dependent extends Node {
  }

  sealed trait Independent extends Node {
    val typ: Value
  }

  private sealed trait Valued extends Independent {
    val value: Value
  }

  private case class DependentWithMeta(dependencies: Seq[Int], metaCount: Int, closure: (Seq[Value], Seq[Value]) => (Seq[Meta], Value)) extends Dependent
  private case class IndependentWithMeta(dependencies: Seq[Int], metas: Seq[Meta], typ: Value) extends Independent
  private case class ValuedWithMeta(dependencies: Seq[Int], metas: Seq[Meta], typ: Value, value: Value) extends Valued

  private sealed trait RestrictionsState
  private object RestrictionsState {
    case class Abstract(tm: Seq[Formula] => System[(Seq[Value], Seq[Value]) => Value]) extends RestrictionsState
    case class Concrete(tm: System[(Seq[Value], Seq[Value]) => Value]) extends RestrictionsState
    case class Valued(tm: System[ValueClosure]) extends RestrictionsState
    val empty = Valued(Map.empty)
  }


  private def nullValues = (0 until 40).map(_ => null: Value).toSeq

  // implicit, dependencies, meta count, (values, metas) => (new_metas, new_value)
  def apply(nodes: Seq[ClosureGraphArguments],
                          dim: Int,
                          tm: Seq[Formula] => System[(Seq[Value], Seq[Value]) => Value]): ClosureGraph = {
    val gs = nodes.map(a => if (a._1.isEmpty) {
      val t = a.map(nullValues, nullValues)
      IndependentWithMeta(a.dependencies, t._1, t._2)
    } else {
      DependentWithMeta(a.dependencies, a.metaCount, a.map)
    })
    ClosureGraph.Impl(gs, dim, if (dim == 0) RestrictionsState.empty else RestrictionsState.Abstract(tm))
  }

  private case class Impl(graph: Seq[ClosureGraph.Node], dimSize: Int, tm: RestrictionsState) extends ClosureGraph {

    def supportShallow(): SupportShallow = {
      val mss = mutable.ArrayBuffer[Meta]()
      val res = graph.map {
        case IndependentWithMeta(ds, ms, typ) =>
          mss.appendAll(ms)
          typ.supportShallow() ++ (ms.toSet: Set[Value.Referential])
        case DependentWithMeta(ds, mc, c) =>
          val res = c(Value.Generic.HACKS, mss.toSeq)
          mss.appendAll(res._1)
          res._2.supportShallow() ++ (res._1.toSet: Set[Value.Referential])
        case _ => logicError()
      }
      res.merge ++
        (if (dimSize == 0) SupportShallow.empty
        else {
          val faces = tm.asInstanceOf[RestrictionsState.Abstract].tm(Formula.Generic.HACKS)
          faces.toSeq.map(f => f._2(Value.Generic.HACKS, mss.toSeq).supportShallow() +- f._1.names).merge
        })
    }

    def fswap(w: Long, z: Formula): ClosureGraph.Impl = {
      val gs = graph.map {
        case IndependentWithMeta(ds, ms, typ) =>
          IndependentWithMeta(ds, ms.map(_.fswap(w, z).asInstanceOf[Value.Meta]), typ.fswap(w, z))
        case DependentWithMeta(ds, mc, c) =>
          DependentWithMeta(ds, mc, (a, b) => {
            val t = c(a, b); (t._1.map(_.fswap(w, z).asInstanceOf[Value.Meta]), t._2.fswap(w, z)) })
        case _ => logicError()
      }
      val zz = if (dimSize == 0) tm else {
        val clo = tm.asInstanceOf[RestrictionsState.Abstract].tm
        RestrictionsState.Abstract(fs => clo(fs).map(pair => (pair._1.fswap(w, z), (v1: Seq[Value], v2: Seq[Value]) => pair._2(v1, v2).fswap(w, z))))
      }
      ClosureGraph.Impl(gs, dimSize, zz)
    }

    def restrict(lv: Assignments): ClosureGraph.Impl = {
      val gs = graph.map {
        case IndependentWithMeta(ds, ms, typ) =>
          IndependentWithMeta(ds, ms.map(_.restrict(lv).asInstanceOf[Value.Meta]), typ.restrict(lv))
        case DependentWithMeta(ds, mc, c) =>
          DependentWithMeta(ds, mc, (a, b) => {
            val t = c(a.map(k => Value.Derestricted(k, lv)), b.map(k => Value.Derestricted(k, lv))); (t._1.map(_.restrict(lv).asInstanceOf[Value.Meta]), t._2.restrict(lv)) })
        case _ => logicError()
      }
      val zz = if (dimSize == 0) tm else {
        val clo = tm.asInstanceOf[RestrictionsState.Abstract].tm
        RestrictionsState.Abstract(fs => clo(fs.map(f => Formula.Derestricted(f, lv))).map(pair =>
          (pair._1.restrict(lv), (v1: Seq[Value], v2: Seq[Value]) => pair._2(v1.map(v => Value.Derestricted(v, lv)), v2.map(v => Value.Derestricted(v, lv))).restrict(lv))))
      }
      ClosureGraph.Impl(gs, dimSize, zz)
    }

    override def phi(): Set[Formula] = tm match {
      case RestrictionsState.Abstract(tm) => logicError()
      case RestrictionsState.Concrete(tm) => tm.keySet
      case RestrictionsState.Valued(tm) => tm.keySet
    }

    override def restrictions(): System[ValueClosure] = tm match {
      case RestrictionsState.Valued(tm) => tm
      case _ => logicError()
    }

    override def reduce(ds: Seq[Formula]): ClosureGraph = {
      tm match {
        case RestrictionsState.Abstract(tm) =>
          assert(ds.size == dimSize)
          val rs = RestrictionsState.Concrete(tm(ds))
          Impl(graph, dimSize, tryReduceRestrictions(graph, rs))
        case _ => logicError()
      }
    }

    def tryReduceRestrictions(grapht: Seq[Node], rs: RestrictionsState): RestrictionsState = {
      rs match {
        case RestrictionsState.Abstract(_) => rs
        case RestrictionsState.Concrete(tm) =>
          if (grapht.forall(_.isInstanceOf[ValuedWithMeta])) {
            val gs = grapht.map(_.asInstanceOf[ValuedWithMeta])
            val vs = gs.map(_.value)
            val ms = gs.flatMap(_.metas)
            RestrictionsState.Valued(tm.view.mapValues(a => () => a.apply(vs, ms)).toMap)
          } else {
            rs
          }
        case RestrictionsState.Valued(_) => rs
      }
    }

    def reduce(i: Int, a: Value): ClosureGraph.Impl = {
      val from = graph
      from(i) match {
        case IndependentWithMeta(ds, mss, typ) =>
          val ns = ValuedWithMeta(ds, mss, typ, a)
          val mms: Seq[Meta] = from.flatMap {
            case DependentWithMeta( _, ms, _) => (0 until ms).map(_ => null)
            case IndependentWithMeta( _, ms, _) => ms
            case ValuedWithMeta(_, ms, _, _) => ms
          }
          val vs = from.indices.map(j => if (j == i) a else from(j) match {
            case ValuedWithMeta(_, _, _, v) => v
            case _ => null
          })
          val grapht = from.map {
            case DependentWithMeta(dss, _, c) if dss.forall(j => vs(j) != null) =>
              val t = c(vs, mms)
              IndependentWithMeta(dss, t._1, t._2)
            case i =>
              i
          }.updated(i, ns)
          ClosureGraph.Impl(grapht, dimSize, tryReduceRestrictions(grapht, tm))
        case _ => logicError()
      }
    }

    def get(name: Int, values: Int => Value): Value = {
      var i = 0
      var g = this
      while (i < name) {
        g = g.reduce(i, values(i))
        i += 1
      }
      g.graph(name).independent.typ
    }
  }

  given isNominal: Nominal[ClosureGraph] {
    def (c: ClosureGraph) supportShallow() = c.asInstanceOf[ClosureGraph.Impl].supportShallow()
    def (c: ClosureGraph) restrict(dav: Assignments) = c.asInstanceOf[ClosureGraph.Impl].restrict(dav)
    def (c: ClosureGraph) fswap(w: Long, z: Formula) = c.asInstanceOf[ClosureGraph.Impl].fswap(w, z)
  }
}


