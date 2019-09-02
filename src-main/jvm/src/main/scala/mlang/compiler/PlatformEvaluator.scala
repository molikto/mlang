package mlang.compiler

import mlang.compiler.Value.Dimension
import mlang.utils.{Benchmark, Name, Text, debug}

import scala.reflect.runtime.currentMirror
import scala.tools.reflect.ToolBox




trait PlatformEvaluator extends Evaluator {

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

    def emitInner(term: Abstract.MetaEnclosedT, d: Int): String = {
      if (term.metas.isEmpty) {
        emit(term.term, d)
      } else {
        s"{ " +
            s"val m$d = new scala.collection.mutable.ArrayBuffer[Meta](); " +
            s"for (_ <- 0 until ${term.metas.size}) m$d.append(Meta(null)); " + // because they might reference each other
            s"${term.metas.zipWithIndex.map(a =>
              s"m$d(${a._2}).state = Meta.Closed(${emit(a._1, d)}); ").mkString("")}" +
            s"${emit(term.term, d)}; " +
            s"}"
      }
    }

    def emitGraph(a: Abstract.ClosureGraph, d: Int): String = {
      val res = a.zipWithIndex.map(pair => {
        val c = pair._1
        val index = pair._2
        val metasBefore = a.take(index).map(_._2.metas.size).sum
        val metaBody = if (c._2.metas.isEmpty) {
          s"(Seq.empty[Value.Meta], ${emit(c._2.term, d)})"
        } else {
          s"{ val m$d = m${d}_.toBuffer; " +
            s"for (k <- 0 until ${c._2.metas.size}) { assert(m$d(k + ${metasBefore}) == null); m$d(k + $metasBefore) = Meta(null)}; " +
            s"${c._2.metas.zipWithIndex.map(k => (k._1, k._2 + metasBefore)).map(a => s"m$d(${a._2}).state = Meta.Closed(${emit(a._1, d)}); ").mkString("")}" +
            s"(m$d.slice($metasBefore, ${metasBefore + c._2.metas.size}).toSeq, ${emit(c._2.term, d)})}"
        }
        s"(Seq[Int](${c._1.mkString(", ")}), ${c._2.metas.size}, (m${d}_, r$d) => $metaBody)"
      }).mkString(", ")
      s"""ClosureGraph.createMetaAnnotated(Seq($res))""".stripMargin
    }

  def emit(id: Option[Abstract.Inductively], d: Int): String = {
    id match {
      case None => "None"
      case Some(a) => s"Some(Inductively(${a.id}, ${a.level}))"
    }
  }

  private def emit(pair: Seq[Abstract.Dimension], depth: Int): String = {
    s"Seq(${pair.map(a => emit(a, depth)).mkString(", ")})"
  }


    def emit(term: Abstract, depth: Int): String = {
      term match {
        case Abstract.Universe(l) =>
          s"Universe($l)"
        case Abstract.Up(l, i) =>
          s"${emit(l, depth)}.up($i)"
        case Abstract.Reference(up, index) =>
          if (up > depth) {
            s"${tunnel(getReference(up - depth - 1, index))}"
          } else {
            if (index == -1) s"r${depth - up}" else s"r${depth - up}($index)"
          }
        case Abstract.MetaReference(up, index) =>
          if (up > depth) {
            s"${tunnel(getMetaReference(up - depth - 1, index))}"
          } else {
            s"m${depth - up}($index)"
          }
        case Abstract.Let(metas, definitions, in) =>
          if (metas.isEmpty && definitions.isEmpty) {
            emit(in, depth + 1)
          } else {
            val d = depth + 1
            s"{ " +
                s"val r$d = new scala.collection.mutable.ArrayBuffer[Reference](); " +
                s"for (_ <- 0 until ${definitions.size}) r$d.append(Reference(null)); " +
                s"val m$d = new scala.collection.mutable.ArrayBuffer[Meta](); " +
                s"for (_ <- 0 until ${metas.size}) m$d.append(Meta(null)); " +
                s"${metas.zipWithIndex.map(a =>
                  s"m$d(${a._2}).state = Meta.Closed(${emit(a._1, d)}); ").mkString("")}" +
                s"${definitions.zipWithIndex.map(a =>
                  s"r$d(${a._2}).value = ${emit(a._1, d)}; ").mkString("")}" +
                s"val body = ${emit(in, d)}; " +
                s"Let(r$d.toSeq, body)" +
                s"}"
          }
        case Abstract.Function(domain, impict, codomain) =>
          val d = depth + 1
          s"Function(${emit(domain, depth)}, $impict, Closure(r$d => ${emitInner(codomain, d)}))"
        case Abstract.Lambda(closure) =>
          val d = depth + 1
          s"Lambda(Closure(r$d => ${emitInner(closure, d)}))"
        case Abstract.App(left, right) =>
          s"App(${emit(left, depth)}, ${emit(right, depth)})"
        case Abstract.Record(id, names, ms, nodes) =>
          val d = depth + 1
          s"""Record( ${emit(id, depth)}, Seq(${names.map(n => source(n)).mkString(", ")}), ${emit(ms)}, ${emitGraph(nodes, d)})"""
        case Abstract.Projection(left, field) =>
          s"Projection(${emit(left, depth)}, $field)"
        case Abstract.Sum(id, constructors) =>
          val d = depth + 1 // we some how have have one layer for the constructor names
          s"""Sum(${emit(id, depth)}, Seq(${constructors.zipWithIndex.map(c =>
            s"Constructor(${source(c._1.name)}, ${emit(c._1.implicits)}, ${emitGraph(c._1.params, d)})").mkString(", ")}))"""
        case Abstract.Maker(sum, field) =>
          s"Maker(${emit(sum, depth)}, $field)"
        case Abstract.PatternLambda(id, dom, codomain, cases) =>
          val d = depth + 1
          s"PatternLambda($id, ${emit(dom, depth)}, Closure(r$d => ${emitInner(codomain, d)}), Seq(${cases.map(c => s"Case(${tunnel(c.pattern)}, MultiClosure(r$d => ${emitInner(c.body, d)}))").mkString(", ")}))"
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
        case Abstract.VType(x, a, b, e) =>
          val d = depth + 1
          s"VType(${emit(x, depth)}, ${emitInner(a, d)}, ${emit(b, depth)}, ${emitInner(e, d)})"
        case Abstract.VMake(x, m, n) =>
          val d = depth + 1
          s"VMake(${emit(x, depth)}, ${emitInner(m, d)}, ${emit(n, depth)})"
        case Abstract.VProj(x, m, f) =>
          s"VProj(${emit(x, depth)}, ${emit(m, depth)}, ${emit(f, depth)})"
        case Abstract.Restricted(t, dir) =>
          s"${emit(t, depth)}.restrict(${emit(dir, depth)})"
      }
    }


  private def emit(pair: Seq[Boolean]): String = {
    s"Seq(${pair.map(_.toString).mkString(", ")})"
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
              case _: Dimension.Internal => logicError()
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

  private def holderSrc(res: String): String = {
      s"""
         |import mlang.utils._
         |import mlang.compiler._
         |import mlang.compiler.Value._
         |
         |
         |new Holder {
         |  def value(ctx: EvaluationContext, vs: Seq[Value], cs: Seq[Closure], ps: Seq[Pattern]) = $res
         |}
       """.stripMargin
  }


  protected def platformEval(term: Abstract): Value = {
    val res = emit(term, -1)
    val src = holderSrc(res)
    debug("==================")
    debug(term)
    debug("==================")
    debug(res)
    debug("==================")
    extractFromHolder(compile[Holder](src))
  }
}