package mlang.compiler

import mlang.utils._

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

  private def source(a: Name): String = "Name(\"" + a.main + "\")"

    def emitInner(term: Abstract.MetaEnclosedT, d: Int): String = {
      if (term.metas.isEmpty) {
        emit(term.term, d)
      } else {
        s"{ " +
            s"val m$d = new scala.collection.mutable.ArrayBuffer[Meta](); " +
            s"for (_ <- 0 until ${term.metas.size}) m$d.append(Meta(null)); " + // because they might reference each other
            s"${term.metas.zipWithIndex.map(a =>
              s"m$d(${a._2}).state = MetaState.Closed(${emit(a._1, d)}); ").mkString("")}" +
            s"${emit(term.term, d)}; " +
            s"}"
      }
    }

    def emitGraph(a: Abstract.ClosureGraph, d: Int): String = {
      val res = a.zipWithIndex.map(pair => {
        val c = pair._1
        val index = pair._2
        val metasBefore = a.take(index).map(_.typ.metas.size).sum
        val metaBody = if (c.typ.metas.isEmpty) {
          s"(Seq.empty[Value.Meta], ${emit(c.typ.term, d)})"
        } else {
          s"{ val m$d = m${d}_.toBuffer; " +
            s"for (k <- 0 until ${c.typ.metas.size}) { assert(m$d(k + ${metasBefore}) == null); m$d(k + $metasBefore) = Meta(null)}; " +
            s"${c.typ.metas.zipWithIndex.map(k => (k._1, k._2 + metasBefore)).map(a => s"m$d(${a._2}).state = MetaState.Closed(${emit(a._1, d)}); ").mkString("")}" +
            s"(m$d.slice($metasBefore, ${metasBefore + c.typ.metas.size}).toSeq, ${emit(c.typ.term, d)})}"
        }
        s"(${c.implicitt}, Seq[Int](${c.deps.mkString(", ")}), ${c.typ.metas.size}, (m${d}_, r$d) => $metaBody)"
      }).mkString(", ")
      s"""ClosureGraph.createMetaAnnotated(Seq($res))""".stripMargin
    }

  def emit(id: Option[Abstract.Inductively], d: Int): String = {
    id match {
      case None => "None"
      case Some(a) => s"Some(Inductively(${a.id}, ${a.level}))"
    }
  }

  private def emit(pair: Seq[Abstract.Formula], depth: Int): String = {
    s"Seq(${pair.map(a => emit(a, depth)).mkString(", ")})"
  }


  def emitFaces(faces: Seq[Abstract.Face], depth: Int) = {
    val d = depth + 2
    s"Seq(${faces.map(a => s"Face(${emit(a.pair, depth)}, AbsClosure(dm$d => ${emitInner(a.body, d)}))").mkString(", ")})"
  }

  def emit(term: Abstract, depth: Int): String = {
      term match {
        case Abstract.Universe(l) =>
          s"Universe($l)"
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
                s"val r$d = new scala.collection.mutable.ArrayBuffer[LocalReference](); " +
                s"for (_ <- 0 until ${definitions.size}) r$d.append(LocalReference(null)); " +
                s"val m$d = new scala.collection.mutable.ArrayBuffer[Meta](); " +
                s"for (_ <- 0 until ${metas.size}) m$d.append(Meta(null)); " +
                s"${metas.zipWithIndex.map(a =>
                  s"m$d(${a._2}).state = MetaState.Closed(${emit(a._1, d)}); ").mkString("")}" +
                s"${definitions.zipWithIndex.map(a =>
                  s"r$d(${a._2}).value = ${emit(a._1, d)}; ").mkString("")}" +
                s"${emit(in, d)}" +
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
        case Abstract.Record(id, names, nodes) =>
          val d = depth + 1
          s"""Record( ${emit(id, depth)}, Seq(${names.map(n => source(n)).mkString(", ")}), ${emitGraph(nodes, d)})"""
        case Abstract.Projection(left, field) =>
          s"Projection(${emit(left, depth)}, $field)"
        case Abstract.Sum(id, constructors) =>
          val d = depth + 1 // we some how have have one layer for the constructor names
          s"""Sum(${emit(id, depth)}, Seq(${constructors.zipWithIndex.map(c =>
            s"Constructor(${source(c._1.name)}, ${emitGraph(c._1.params, d)})").mkString(", ")}))"""
        case Abstract.Make(vs) =>
          s"Make(${vs.map(v => emit(v, depth))})"
        case Abstract.Construct(name, vs) =>
          s"Construct($name, ${vs.map(v => emit(v, depth))})"
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
        case Abstract.Transp(tp, dir, base) =>
          val d = depth + 1
          s"Transp(AbsClosure(dm$d => ${emitInner(tp, d)}), ${emit(dir, depth)}, ${emit(base, depth)})"
        case Abstract.Hcomp(tp, base, faces) =>
          s"Hcomp(" +
              s"${emit(tp, depth)}, " +
              s"${emit(base, depth)}, " +
              emitFaces(faces, depth) +
              s")"
        case Abstract.Comp(tp, base, faces) =>
          s"Comp(" +
              s"AbsClosure(dm${depth + 1} => ${emitInner(tp, depth + 1)}), " +
              s"${emit(base, depth)}, " +
              emitFaces(faces, depth) +
              s")"
        case Abstract.GlueType(tp, faces) =>
          s"GlueType(" +
              s"${emit(tp, depth)}, " +
              emitFaces(faces, depth) +
              s")"
        case Abstract.Glue(base, faces) =>
          s"Glue(" +
              s"${emit(base, depth)}, " +
              emitFaces(faces, depth) +
              s")"
        case Abstract.Unglue(tp, base, faces) =>
          s"Unglue(" +
              s"${emit(tp, depth)}, " +
              s"${emit(base, depth)}, " +
              emitFaces(faces, depth) +
              s")"
      }
    }


  private def emit(pair: Seq[Boolean]): String = {
    s"Seq(${pair.map(_.toString).mkString(", ")})"
  }



    private def emit(dim: Abstract.Formula, depth: Int): String = {
      dim match {
        case Abstract.Formula.Reference(up) =>
          if (up > depth) {
            tunnel(getDimension(up - depth - 1))
          } else {
            s"dm${depth - up}"
          }
        case Abstract.Formula.True =>
          s"Formula.True"
        case Abstract.Formula.False =>
          s"Formula.False"
        case Abstract.Formula.And(l, r) =>
          s"Formula.And(${emit(l, depth)}, ${emit(r, depth)})"
        case Abstract.Formula.Or(l, r) =>
          s"Formula.Or(${emit(l, depth)}, ${emit(r, depth)})"
        case Abstract.Formula.Neg(l) =>
          s"Formula.Neg(${emit(l, depth)})"
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
         |  def value(ctx: EvaluatorContext, vs: Seq[Any]) = $res
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
