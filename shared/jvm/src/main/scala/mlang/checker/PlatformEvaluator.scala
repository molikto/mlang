package mlang.core

import mlang.core.Value.Dimension
import mlang.name.Name
import mlang.utils.{Text, debug}

import scala.reflect.runtime.currentMirror
import scala.tools.reflect.ToolBox



trait PlatformEvaluator extends BaseEvaluator {

  private def compile[A](string: String): A = {
    val toolbox = currentMirror.mkToolBox()
    val tree = toolbox.parse(string)
    toolbox.eval(tree).asInstanceOf[A]
  }

  private def source(a: Text): String = "Text(\"" + a.string + "\")"

  private def source(a: Name): String = "Name(\"" + a.main + "\")"



  private class Emitter(recursivelyDefining: Set[Int]) {
    def emit(term: Abstract, depth: Int): String = {
      term match {
        case Abstract.Universe(l) =>
          s"Universe($l)"
        case Abstract.TermReference(up, index, closed) =>
          if (up > depth) {
            if (up == depth + 1 && recursivelyDefining.contains(index)) {
              // eval recursive, this deref happens under a closure, so it will have a value
              assert(closed == 1)
              s"Reference(rs($index), $closed).deref(r)"
            } else {
              // this is a value inside the context
              assert((up == depth + 1 && closed == 0) || closed == -1)
              s"${tunnel(evalOpenTermReferenceAsReference(up - depth - 1, index))}.deref(r)"
            }
          } else {
            // a reference inside the emit context
            if (closed >= 0) {
              // reference to a value directly
              s"Reference(r${depth - up}($index), $closed).deref(r)"
            } else {
              // formal parameters of a closure
              s"r${depth - up}($index).renormalize(r)"
            }
          }
        case Abstract.Let(definitions, order, in) =>
          if (definitions.isEmpty) {
            emit(in, depth + 1)
          } else {
            val d = depth + 1
            s"{val r$d = new scala.collection.mutable.ArrayBuffer[Value](); " +
                s"for (_ <- 0 until ${definitions.size}) r$d.append(null); " +
                s"${order.map(a =>
                  s"r$d.update($a, ${emit(definitions(a), d)})"
                ).mkString("; ")}; " +
                s"val body = ${emit(in, d)}; " +
                s"Let(r$d, Seq(${order.mkString(", ")}), body).delet(r)" +
                s"}"
          }
        case Abstract.Function(domain, codomain) =>
          val d = depth + 1
          s"Function(${emit(domain, depth)}, Closure((r$d, r) => ${emit(codomain, d)}))"
        case Abstract.Lambda(closure) =>
          val d = depth + 1
          s"Lambda(Closure((r$d, r) => ${emit(closure, d)}))"
        case Abstract.Application(left, right) =>
          s"${emit(left, depth)}.app(${emit(right, depth)}, r)"
        case Abstract.Record(level, nodes) =>
          val d = depth + 1
          s"""Record($level, Seq(${nodes.zipWithIndex.map(c =>
            s"{ val ds = Seq[Int](${c._1.dependencies.mkString(", ")}); " +
                s"RecordNode(" +
                s"${source(c._1.name)}, " +
                s"ds, " +
                s"MultiClosure((jd, r) => { def r$d(i: Int): Value = jd(ds.indexOf(i)); ${emit(c._1.typ, d)}}))}").mkString(", ")}))"""
        case Abstract.Projection(left, field) =>
          s"${emit(left, depth)}.project($field, r)"
        case Abstract.Sum(level, constructors) =>
          val d = depth + 1 // we some how have have one layer for the constructor names
          s"""Sum($level, ${constructors.zipWithIndex.map(c =>
            s"Constructor(${source(c._1.name)}, ${c._1.params.size}, Seq(${c._1.params.map(p => s"MultiClosure((r$d, r) => " + emit(p, d) + ")").mkString(", ")}))")})"""
        case Abstract.Maker(sum, field) =>
          s"${emit(sum, depth)}.demaker($field, r)"
        case Abstract.PatternLambda(id, codomain, cases) =>
          val d = depth + 1
          s"PatternLambda($id, Closure((r$d, r) => ${emit(codomain, d)}), Seq(${cases.map(c => s"Case(${tunnel(c.pattern)}, MultiClosure((r$d, r) => ${emit(c.body, d)}))").mkString(", ")}))"
        case Abstract.PathApplication(left, r) =>
          s"${emit(left, depth)}.papp(${emit(r, depth)}, r)"
        case Abstract.PathLambda(body) =>
          val d = depth + 1
          s"PathLambda(PathClosure((dm$d, r) => ${emit(body, d)}))"
        case Abstract.PathType(typ, left, right) =>
          val d = depth + 1
          s"PathType(PathClosure((dm$d, r) => ${emit(typ, d)}), ${emit(left, depth)}, ${emit(right, depth)})"
      }
    }


    private def emit(dim: Abstract.Dimension, depth: Int): String = {
      dim match {
        case Abstract.Dimension.Reference(up) =>
          if (up > depth) {
            getDimension(up - depth - 1) match {
              case Dimension.OpenReference(id) =>
                s"Dimension.OpenReference($id)"
              case Dimension.Constant(isOne) =>
                s"Dimension.Constant($isOne)"
            }
          } else {
            s"dm${depth - up}"
          }
        case Abstract.Dimension.Constant(isOne) =>
          s"Dimension.Constant($isOne)"
      }
    }
  }
  protected def platformEvalRecursive(terms: Map[Int, Abstract], reduction: Reduction): Map[Int, Value] = {
    val emitter = new Emitter(terms.keySet)
    val rr = new scala.collection.mutable.ArrayBuffer[Value]()
    for (_ <- 0 to terms.keySet.max) rr.append(null)
    for (t <- terms) {
      val res = emitter.emit(t._2, -1)
      val src = holderSrc(res)
      debug("==================")
      debug(t._2)
      debug("==================")
      debug(res)
      debug("==================")
      rr.update(t._1, extractFromHolder(compile[Holder](src), reduction, rr))
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
         |  def value(ctx: Context, r: Reduction, rs: Seq[Value], vs: Seq[Value], cs: Seq[Closure], ps: Seq[Pattern]) = $res
         |}
       """.stripMargin
  }


  protected def platformEval(term: Abstract, reduction: Reduction): Value = {
    val res = new Emitter(Set.empty).emit(term, -1)
    val src = holderSrc(res)
    debug("==================")
    debug(term)
    debug("==================")
    debug(res)
    debug("==================")
    extractFromHolder(compile[Holder](src), reduction, Seq.empty)
  }
}
