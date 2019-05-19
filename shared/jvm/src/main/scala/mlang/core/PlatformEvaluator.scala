package mlang.core

import mlang.core.Value.Dimension
import mlang.name.Name
import mlang.utils.{Benchmark, Text, debug}

import scala.reflect.runtime.currentMirror
import scala.tools.reflect.ToolBox




trait PlatformEvaluator extends BaseEvaluator {

  private def compile[A](string: String): A = Benchmark.HoasCompile {
    try {
      val toolbox = currentMirror.mkToolBox()
      val tree = toolbox.parse(string)
      toolbox.eval(tree).asInstanceOf[A]
    } catch {
      case e: Throwable => throw PlatformEvaluatorException(string, e)
    }
  }

  private def source(a: Text): String = "Text(\"" + a.string + "\")"

  private def source(a: Name): String = "Name(\"" + a.main + "\")"



  private class Emitter(recursivelyDefining: Set[Int]) {
    def emitInner(term: Abstract.ClosureT, depth: Int): String = {
      s"{ val m$depth = Seq(${term.metas.map(a => emit(a, depth)).mkString(", ")}); ${emit(term.term, depth)} }"
    }

    def emitGraph(a: Abstract.ClosureGraph, d: Int): String = {
      s"""ClosureGraph.createTemp(Seq(${a.map(c => "(Seq[Int](" + c._1.mkString(", ") + "), " + s"r$d => ${emitInner(c._2, d)})").mkString(", ")}))""".stripMargin
    }

    def emit(term: Abstract, depth: Int): String = {
      term match {
        case Abstract.Universe(l) =>
          s"Universe($l)"
        case Abstract.Reference(up, index, closed) =>
          if (up > depth) {
            if (up == depth + 1 && recursivelyDefining.contains(index)) {
              // eval recursive, this deref happens under a closure, so it will have a value
              assert(closed)
              s"rs($index)"
            } else {
              // this is a value inside the context
              s"${tunnel(evalTermReferenceAsReference(up - depth - 1, index, closed))}"
            }
          } else {
            if (index == -1) s"r${depth - up}" else s"r${depth - up}($index)"
          }
        case Abstract.Let(metas, definitions, order, in) =>
          if (definitions.isEmpty) {
            emit(in, depth + 1)
          } else {
            val d = depth + 1
            s"{val r$d = new scala.collection.mutable.ArrayBuffer[Reference](); " +
                s"for (_ <- 0 until ${definitions.size}) r$d.append(Reference(null)); " +
                s"${order.map(a =>
                  s"r$d($a).value = ${emit(definitions(a), d)}; "
                ).mkString("")}" +
                s"val body = ${emit(in, d)}; " +
                s"Let(r$d, Seq(${order.mkString(", ")}), body)" +
                s"}"
          }
        case Abstract.Function(domain, codomain) =>
          val d = depth + 1
          s"Function(${emit(domain, depth)}, Closure(r$d => ${emitInner(codomain, d)}))"
        case Abstract.Lambda(closure) =>
          val d = depth + 1
          s"Lambda(Closure(r$d => ${emitInner(closure, d)}))"
        case Abstract.App(left, right) =>
          s"App(${emit(left, depth)}, ${emit(right, depth)})"
        case Abstract.Record(level, names, nodes) =>
          val d = depth + 1
          s"""Record($level, Seq(${names.map(n => source(n)).mkString(", ")}), ${emitGraph(nodes, d)})"""
        case Abstract.Projection(left, field) =>
          s"Project(${emit(left, depth)}, $field)"
        case Abstract.Sum(level, constructors) =>
          val d = depth + 1 // we some how have have one layer for the constructor names
          s"""Sum($level, Seq(${constructors.zipWithIndex.map(c =>
            s"Constructor(${source(c._1.name)}, ${emitGraph(c._1.params, d)})").mkString(", ")}))"""
        case Abstract.Maker(sum, field) =>
          s"Maker(${emit(sum, depth)}, $field)"
        case Abstract.PatternLambda(id, codomain, cases) =>
          val d = depth + 1
          s"PatternLambda($id, Closure(r$d => ${emitInner(codomain, d)}), Seq(${cases.map(c => s"Case(${tunnel(c.pattern)}, MultiClosure(r$d => ${emitInner(c.body, d)}))").mkString(", ")}))"
        case Abstract.PathApp(left, right) =>
          s"PathApp(${emit(left, depth)}, ${emit(right, depth)})"
        case Abstract.PathLambda(body) =>
          val d = depth + 1
          s"PathLambda(AbsClosure(dm$d => ${emitInner(body, d)}))"
        case Abstract.PathType(typ, left, right) =>
          val d = depth + 1
          s"PathType(AbsClosure(dm$d => ${emitInner(typ, d)}), ${emit(left, depth)}, ${emit(right, depth)})"
        case Abstract.Coe(dir, tp, base) =>
          val d = depth + 1
          s"Coe(${emit(dir, depth)}, AbsClosure(dm$d => ${emitInner(tp, d)}), ${emit(base, depth)})"
        case Abstract.Hcom(dir, tp, base, faces) =>
          val d = depth + 2
          s"Hcom(${emit(dir, depth)}, " +
              s"${emit(tp, depth)}, " +
              s"${emit(base, depth)}, " +
              s"Seq(${faces.map(a => s"Face(${emit(a.pair, depth)}, AbsClosure(dm$d => ${emitInner(a.body, d)}))").mkString(", ")})" +
              s")"
        case Abstract.Com(dir, tp, base, faces) =>
          val d = depth + 2
          s"Com(${emit(dir, depth)}, " +
              s"AbsClosure(dm${depth + 1} => ${emitInner(tp, depth + 1)}), " +
              s"${emit(base, depth)}, " +
              s"Seq(${faces.map(a => s"Face(${emit(a.pair, depth)}, AbsClosure(dm$d => ${emitInner(a.body, d)}))").mkString(", ")})" +
              s")"
        case Abstract.Restricted(t, dir) =>
          s"${emit(t, depth)}.restrict(${emit(dir, depth)})"
      }
    }

    private def emit(pair: Abstract.DimensionPair, depth: Int): String = {
      s"DimensionPair(${emit(pair.from, depth)}, ${emit(pair.to, depth)})"
    }

    private def emit(dim: Abstract.Dimension, depth: Int): String = {
      dim match {
        case Abstract.Dimension.Reference(up) =>
          if (up > depth) {
            getDimension(up - depth - 1) match {
              case Dimension.Generic(id) =>
                s"Dimension.Generic($id)"
              case Dimension.True =>
                s"Dimension.True"
              case Dimension.False =>
                s"Dimension.False"
            }
          } else {
            s"dm${depth - up}"
          }
        case Abstract.Dimension.True =>
          s"Dimension.True"
        case Abstract.Dimension.False =>
          s"Dimension.False"
        case Abstract.Dimension.Restricted(d, pair) =>
          s"${emit(d, depth)}.restrict(${emit(pair, depth)})"
      }
    }
  }
  protected def platformEvalRecursive(terms: Map[Int, Abstract]): Map[Int, Value] = {
    val emitter = new Emitter(terms.keySet)
    val rr = new scala.collection.mutable.ArrayBuffer[Value.Reference]()
    for (_ <- 0 to terms.keySet.max) rr.append(Value.Reference(null))
    for (t <- terms) {
      val res = emitter.emit(t._2, -1)
      val src = holderSrc(res)
      debug("==================")
      debug(t._2)
      debug("==================")
      debug(res)
      debug("==================")
      rr(t._1).value = extractFromHolder(compile[Holder](src), rr)
    }
    Map.empty ++ terms.transform((f, _) => rr(f))
  }

  private def holderSrc(res: String): String = {
      s"""
         |import mlang.name.Name
         |import mlang.core._
         |import mlang.core.Value._
         |import mlang.utils.Text
         |
         |
         |new Holder {
         |  def value(ctx: Context, rs: Seq[Value], vs: Seq[Value], cs: Seq[Closure], ps: Seq[Pattern]) = $res
         |}
       """.stripMargin
  }


  protected def platformEval(term: Abstract): Value = {
    val res = new Emitter(Set.empty).emit(term, -1)
    val src = holderSrc(res)
    debug("==================")
    debug(term)
    debug("==================")
    debug(res)
    debug("==================")
    extractFromHolder(compile[Holder](src), Seq.empty)
  }
}
