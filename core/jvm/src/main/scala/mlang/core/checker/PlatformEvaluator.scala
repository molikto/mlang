package mlang.core.checker

import mlang.core.checker.Value.OpenReference
import mlang.core.name.Name
import mlang.core.utils.{Text, debug}

import scala.reflect.runtime.currentMirror
import scala.tools.reflect.ToolBox


trait PlatformHolder extends Holder {

}

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
        case Abstract.Reference(up, index, closed) =>
          if (up > depth) {
            if (up == depth + 1 && recursivelyDefining.contains(index)) {
              assert(closed == 1)
              s"rs($index)"
            } else {
              assert((up == depth + 1 && closed == 0) || closed == -1)
              s"${tunnel(evalClosedReference(up - depth - 1, index))}.deref()"
            }
          } else {
            if (closed == 1) {
              // first case is for non-guarded (inductive), and r.value actually is null, it will be filled latter
              // second is for guarded
              s"r${depth - up}($index) match { case r: RecursiveReference => r; case a => RecursiveReference(a) }"
            } else if (closed == 0) {
              s"Reference(r${depth - up}($index))"
            } else {
              s"r${depth - up}($index)"
            }
          }
        case Abstract.Function(domain, codomain) =>
          val d = depth + 1
          s"Function(${emit(domain, depth)}, r$d => ${emit(codomain, d)})"
        case Abstract.Lambda(closure) =>
          val d = depth + 1
          s"Lambda(r$d => ${emit(closure, d)})"
        case Abstract.Application(left, right) =>
          s"${emit(left, depth)}.app(${emit(right, depth)})"
        case Abstract.Record(level, nodes) =>
          val d = depth + 1
          s"""Record($level, ${nodes.zipWithIndex.map(c => s"RecordNode(${source(c._1.name)}, Seq(${nodes.take(c._2).map(a => source(a.name.refSelf)).mkString(", ")}), r$d => ${emit(c._1.typ, d)})")})"""
        case Abstract.RecordMaker(record) =>
          s"${emit(record, depth)}.asInstanceOf[Record].maker"
        case Abstract.Projection(left, field) =>
          s"${emit(left, depth)}.project($field)"
        case Abstract.Sum(level, constructors) =>
          val d = depth + 2 // we some how have have one layer for the constructor names
          s"""Sum($level, ${constructors.zipWithIndex.map(c => s"Constructor(${source(c._1.name)}, ${c._1.params.size}, Seq(${c._1.params.map(p => s"r$d => " + emit(p, d)).mkString(", ")}))")})"""
        case Abstract.SumMaker(sum, field) =>
          s"${emit(sum, depth)}.asInstanceOf[Sum].constructors($field).maker"
        case Abstract.Let(definitions, order, in) =>
          val d = depth + 1
          s"{val r$d = new scala.collection.mutable.ArrayBuffer[Value](); " +
              s"for (_ <- 0 until ${definitions.size}) r$d.append(RecursiveReference(null)); " +
              s"${order.flatten.map(a => s"r$d.update($a, ${emit(definitions(a), d)})").mkString("; ")}; ${emit(in, d)}}"
        case Abstract.PatternLambda(codomain, cases) =>
          val d = depth + 1
          s"PatternLambda(${tunnel(codomain)}, Seq(${cases.map(c => s"Case(${tunnel(c.pattern)}, r$d => ${emit(c.body, d)})").mkString(", ")}))"
      }
    }
  }


  protected def platformEvalRecursive(terms: Map[Int, Abstract]): Map[Int, Value] = {
    val emitter = new Emitter(terms.keySet)
    val vs = Map.empty ++ terms.mapValues(_ => Value.RecursiveReference(null))
    val nvs = Map.empty ++ terms.mapValues(abs => {
      val res = emitter.emit(abs, -1)
      val src = holderSrc(res)
      debug("==================")
      debug(abs)
      debug("==================")
      debug(res)
      debug("==================")
      extractFromHolder(compile[Holder](src), vs)
    })
    for (vv <- vs) {
      vv._2.value = nvs(vv._1)
    }
    nvs
  }

  private def holderSrc(res: String): String = {
      s"""
         |import mlang.core.name.Name
         |import mlang.core.checker._
         |import mlang.core.checker.Value._
         |import mlang.core.utils.Text
         |
         |
         |new PlatformHolder {
         |  def value(ctx: Context, rs: Map[Int, Value], vs: Seq[Value], cs: Seq[Closure], ps: Seq[Pattern]) = $res
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
    extractFromHolder(compile[Holder](src), Map.empty).asInstanceOf[Value]
  }
}
