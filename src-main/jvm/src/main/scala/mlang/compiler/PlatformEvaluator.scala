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

  def emitClosure(c: Abstract.Closure, depth: Int): String = {
    val d = depth + 1
    s"Closure(r$d => ${emitInner(c, d)})"
  }

  def emitAbsClosure(c: Abstract.AbsClosure, depth: Int): String = {
    val d = depth + 1
    s"AbsClosure(dm$d => ${emitInner(c, d)})"
  }

  def emitMultiClosure(c: Abstract.MultiClosure, depth: Int, noDim: Boolean = false): String = {
    val d = depth + 1
    val dim = if (noDim) "_" else s"dm$d"
    s"MultiClosure((r$d,$dim) => ${emitInner(c, d)})"
  }


    def emitGraph(a: Abstract.ClosureGraph, depth: Int): String = {
      val d = depth + 1
      val res = a.nodes.zipWithIndex.map(pair => {
        val c = pair._1
        val index = pair._2
        val metasBefore = a.nodes.take(index).map(_.typ.metas.size).sum
        val metaBody = if (c.typ.metas.isEmpty) {
          s"(Seq.empty[Value.Meta], ${emit(c.typ.term, d)})"
        } else {
          s"{ val m$d = m${d}_.asInstanceOf[Seq[Meta]].toBuffer; " +
            s"for (k <- 0 until ${c.typ.metas.size}) { assert(m$d(k + ${metasBefore}) == null); m$d(k + $metasBefore) = Meta(null)}; " +
            s"${c.typ.metas.zipWithIndex.map(k => (k._1, k._2 + metasBefore)).map(a => s"m$d(${a._2}).state = MetaState.Closed(${emit(a._1, d)}); ").mkString("")}" +
            s"(m$d.slice($metasBefore, ${metasBefore + c.typ.metas.size}).toSeq, ${emit(c.typ.term, d)})}"
        }
        s"(${c.implicitt}, Seq[Int](${c.deps.mkString(", ")}), ${c.typ.metas.size}, (m${d}_, r$d) => $metaBody)"
      }).mkString(", ")
      val kkk = s"Seq(${a.restrictions.toSeq.map(a => s"(${emit(a._1, d)}, (m$d: Seq[Value], r$d: Seq[Value]) => ${emitInner(a._2, d + 1)})").mkString(", ")}).toMap"
      s"""ClosureGraph.createMetaAnnotated(Seq($res), ${a.dims}, (dm$d: Seq[Formula]) => $kkk)""".stripMargin
    }

  def emit(id: Option[Abstract.Inductively], depth: Int): String = {
    id match {
      case None => "None"
      case Some(a) => s"Some(Inductively(${a.id}, ${emit(a.typ, depth)}, Seq[Value](${a.ps.map(k => emit(k, depth)).mkString(", ")})))"
    }
  }

  private def emit(pair: Seq[Abstract.Formula], depth: Int): String = {
    s"Seq(${pair.map(a => emit(a, depth)).mkString(", ")})"
  }


  def emitAbsClosureSystem(faces: Abstract.AbsClosureSystem, depth: Int) = {
    if (faces.isEmpty) "AbsClosureSystem.empty" else s"Seq(${faces.toSeq.map(a => s"(${emit(a._1, depth)}, ${emitAbsClosure(a._2, depth + 1)})").mkString(", ")}).toMap"
  }

  def emitMultiClosureSystem(faces: Abstract.MultiClosureSystem, depth: Int, noDim: Boolean = true) = {
    if (faces.isEmpty) {
      "MultiClosureSystem.empty"
    } else {
      val d = depth + 2
      val dim = if (noDim) "_" else s"dm$d"
      s"Seq(${faces.toSeq.map(a => s"(${emit(a._1, depth)}, ${emitMultiClosure(a._2, depth + 1, noDim)})").mkString(", ")}).toMap"
    }
  }

  def emitEnclosedSystem(faces: Abstract.EnclosedSystem, depth: Int) = {
    // it evals to a value system.
    if (faces.isEmpty) "Map.empty" else s"Seq(${faces.toSeq.map(a => s"(${emit(a._1, depth)}, ${emitInner(a._2, depth + 2)})").mkString(", ")}).toMap"
  }

  def emitConstructor(c: Abstract.Constructor, depth: Int) = {
    s"Constructor(" +
      s"${source(c.name)}, " +
      s"${emitGraph(c.params, depth)})"
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
          s"Function(${emit(domain, depth)}, $impict, ${emitClosure(codomain, depth)})"
        case Abstract.Lambda(closure) =>
          s"Lambda(${emitClosure(closure, depth)})"
        case Abstract.App(left, right) =>
          s"App(${emit(left, depth)}, ${emit(right, depth)})"
        case Abstract.Record(id, names, nodes) =>
          s"""Record( ${emit(id, depth)}, Seq(${names.map(n => source(n)).mkString(", ")}), ${emitGraph(nodes, depth)})"""
        case Abstract.Projection(left, field) =>
          s"Projection(${emit(left, depth)}, $field)"
        case Abstract.Sum(id, constructors) =>
          s"""Sum(${emit(id, depth)}, Seq(${constructors.map(c => emitConstructor(c, depth)).mkString(", ")}))"""
        case Abstract.Make(vs) =>
          s"Make(${vs.map(v => emit(v, depth))})"
        case Abstract.Construct(name, vs, ds, ty) =>
          s"Construct($name, ${vs.map(v => emit(v, depth))}, ${ds.map(d => emit(d, depth))}, ${emitEnclosedSystem(ty, depth)})"
        case Abstract.PatternLambda(id, dom, codomain, cases) =>
          s"PatternLambda($id, ${emit(dom, depth)}, ${emitClosure(codomain, depth)}, Seq(${cases.map(c => s"Case(${tunnel(c.pattern)}, ${emitMultiClosure(c.body, depth)})").mkString(", ")}))"
        case Abstract.PathApp(left, right) =>
          s"PathApp(${emit(left, depth)}, ${emit(right, depth)})"
        case Abstract.PathLambda(body) =>
          s"PathLambda(${emitAbsClosure(body, depth)})"
        case Abstract.PathType(typ, left, right) =>
          s"PathType(${emitAbsClosure(typ, depth)}, ${emit(left, depth)}, ${emit(right, depth)})"
        case Abstract.Transp(tp, dir, base) =>
          s"Transp(${emitAbsClosure(tp, depth)}, ${emit(dir, depth)}, ${emit(base, depth)})"
        case Abstract.Hcomp(tp, base, faces) =>
          s"Hcomp(" +
              s"${emit(tp, depth)}, " +
              s"${emit(base, depth)}, " +
              emitAbsClosureSystem(faces, depth) +
              s")"
        case Abstract.Comp(tp, base, faces) =>
          s"Comp(" +
              s"${emitAbsClosure(tp, depth)}, " +
              s"${emit(base, depth)}, " +
              emitAbsClosureSystem(faces, depth) +
              s")"
        case Abstract.GlueType(tp, faces) =>
          s"GlueType(" +
              s"${emit(tp, depth)}, " +
              emitEnclosedSystem(faces, depth) +
              s")"
        case Abstract.Glue(base, faces) =>
          s"Glue(" +
              s"${emit(base, depth)}, " +
            emitEnclosedSystem(faces, depth) +
              s")"
        case Abstract.Unglue(tp, base, faces) =>
          s"Unglue(" +
              s"${emit(tp, depth)}, " +
              s"${emit(base, depth)}, " +
            emitEnclosedSystem(faces, depth) +
              s")"
      }
    }


  private def emit(pair: Seq[Boolean]): String = {
    s"Seq(${pair.map(_.toString).mkString(", ")})"
  }



    private def emit(dim: Abstract.Formula, depth: Int): String = {
      dim match {
        case Abstract.Formula.Reference(up, index) =>
          if (up > depth) {
            tunnel(getDimension(up - depth - 1, index))
          } else {
            if (index == -1) s"dm${depth - up}" else s"dm${depth - up}($index)"
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
