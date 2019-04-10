package mlang.core.checker

import mlang.core.utils.{Text, debug}

import scala.collection.mutable
import scala.reflect.runtime.currentMirror
import scala.tools.reflect.ToolBox



trait Evaluator extends BaseEvaluator {

  private def compile[A](string: String): A = {
    val toolbox = currentMirror.mkToolBox()
    val tree = toolbox.parse(string)
    toolbox.eval(tree).asInstanceOf[A]
  }

  private def source(a: Text): String = "Text(\"" + a.string + "\")"

  private def emit(term: Abstract, depth: Int): String = {
    term match {
      case Abstract.AbstractReference(up, index, name) =>
        // TODO closed reference
        if (up > depth) s"ctx.get(${up - depth - 1}, $index).value.get"
        else s"r${depth - up}($index)"
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
        s"""Record($level, ${nodes.zipWithIndex.map(c => s"RecordNode(${c._1.name}, Seq(${nodes.take(c._2).map(a => source(a.name)).mkString(", ")}), r$d => ${emit(c._1.typ, d)})")})"""
      case Abstract.RecordMaker(record) =>
        s"${emit(record, depth)}.make"
      case Abstract.Projection(left, field) =>
        s"${emit(left, depth)}.project($field)"
      case Abstract.Sum(level, constructors) =>
        val d = depth + 1
        s"""Sum($level, ${constructors.zipWithIndex.map(c => s"Constructor(${c._1.name}, r$d => ${c._1.params.map(p => emit(p, d)).mkString(", ")})")})"""
      case Abstract.SumMaker(sum, field) =>
        s"${emit(sum, depth)}.constructors($field).make"
      case Abstract.Let(definitions, in) =>
        val d = depth + 1
        s"val r$d = new scala.collection.mutable.ArrayBuffer[Value](); ${definitions.map(a => s"r$d.append(${emit(a, d)})").mkString("; ")}; ${emit(in, d)}"
      case Abstract.PatternLambda(codomain, cases) =>
        val d = depth + 1
        s"PatternLambda(${tunnel(codomain)}, Seq(${cases.map(c => s"Case(${tunnel(c.pattern)}, r$d => ${emit(c.body, d)})").mkString(", ")}))"
    }
  }



  def platformEval(term: Abstract): Value = {
    val src =
      s"""
         |import mlang.core.checker._
         |import mlang.core.checker.Value._
         |import mlang.core.utils.Text
         |
         |object H extends Holder {
         |  def value(ctx: Context, vs: Seq[Value], cs: Seq[Closure], ps: Seq[Pattern]) = ${emit(term, -1)}
         |}
       """.stripMargin

    debug("==================")
    debug(term)
    debug("==================")
    debug(src)
    debug("==================")
    extractFromHolder(compile[Holder](src))
  }
}
