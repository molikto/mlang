package mlang.core.checker

import mlang.core.name.Name
import mlang.core.utils.{Text, debug}

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
        case Abstract.Reference(up, index, closed) =>
          if (up > depth) {
            if (up == depth + 1 && recursivelyDefining.contains(index)) {
              // eval recursive, this deref happens under a closure, so it will have a value
              assert(closed == 1)
              s"RecursiveReference(rs($index)._1, rs($index)._2).deref(r)"
            } else {
              // this is a value inside the context
              assert((up == depth + 1 && closed == 0) || closed == -1)
              s"${tunnel(evalOpenAsReference(up - depth - 1, index))}.deref(r)"
            }
          } else {
            // a reference inside the emit context
            if (closed == 1) {
              s"RecursiveReference(r${depth - up}($index).value, r${depth - up}($index).typ.get).deref(r)"
            } else if (closed == 0) {
              // reference to a value directly
              s"Reference(r${depth - up}($index)).deref(r)"
            } else {
              // formal parameters of a closure
              s"r${depth - up}($index)"
            }
          }
        case Abstract.Let(definitions, order, in) =>
          val d = depth + 1
          s"{val r$d = new scala.collection.mutable.ArrayBuffer[Let.Item](); " +
          s"for (_ <- 0 until ${definitions.size}) r$d.append(null); " +
          s"${order.flatten.map(a =>
            s"r$d.update($a, Let.Item(${emit(definitions(a).value, d)}, ${definitions(a).typ.map(j => "Some(" + emit(j, d) + ")").getOrElse("None")}))"
          ).mkString("; ")}; " +
          s"val body = ${emit(in, d)}; " +
          s"Let(r$d, body).delet(r)" +
          s"}"
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
          s"""Record($level, ${nodes.zipWithIndex.map(c =>
            s"RecordNode(${source(c._1.name)}, Seq(${nodes.take(c._2).map(a => source(a.name.refSelf)).mkString(", ")}), MultiClosure((r$d, r) => ${emit(c._1.typ, d)}))")})"""
        case Abstract.RecordMaker(record) =>
          s"${emit(record, depth)}.asInstanceOf[Record].maker"
        case Abstract.Projection(left, field) =>
          s"${emit(left, depth)}.project($field, r)"
        case Abstract.Sum(level, constructors) =>
          val d = depth + 2 // we some how have have one layer for the constructor names
          s"""Sum($level, ${constructors.zipWithIndex.map(c =>
            s"Constructor(${source(c._1.name)}, ${c._1.params.size}, Seq(${c._1.params.map(p => s"MultiClosure((r$d, r) => " + emit(p, d) + ")").mkString(", ")}))")})"""
        case Abstract.SumMaker(sum, field) =>
          s"${emit(sum, depth)}.asInstanceOf[Sum].constructors($field).maker"
        case Abstract.PatternLambda(id, codomain, cases) =>
          val d = depth + 1
          s"PatternLambda($id, Closure((r$d, r) => ${emit(codomain, d)}), Seq(${cases.map(c => s"Case(${tunnel(c.pattern)}, MultiClosure((r$d, r) => ${emit(c.body, d)}))").mkString(", ")}))"
      }
    }
  }


  protected def platformEvalRecursive(terms: Map[Int, (Abstract, Value)], reduction: Reduction): Map[Int, Value] = {
    val emitter = new Emitter(terms.keySet)
    val rr = new scala.collection.mutable.ArrayBuffer[(Value, Value)]()
    for (_ <- 0 to terms.keySet.max) rr.append(null)
    for (t <- terms) {
      val res = emitter.emit(t._2._1, -1)
      val src = holderSrc(res)
      debug("==================")
      debug(t._2)
      debug("==================")
      debug(res)
      debug("==================")
      rr.update(t._1, (extractFromHolder(compile[Holder](src), reduction, rr), t._2._2))
    }
    Map.empty ++ terms.transform((f, _) => rr(f)._1)
  }

  private def holderSrc(res: String): String = {
      s"""
         |import mlang.core.name.Name
         |import mlang.core.checker._
         |import mlang.core.checker.Value._
         |import mlang.core.utils.Text
         |
         |
         |new Holder {
         |  def value(ctx: Context, r: Reduction, rs: Seq[(Value, Value)], vs: Seq[Value], cs: Seq[Closure], ps: Seq[Pattern]) = $res
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
