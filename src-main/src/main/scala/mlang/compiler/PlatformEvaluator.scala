package mlang.compiler

import mlang.compiler.semantic.Formula.Assignments
import mlang.compiler.Value.SupportShallow
import mlang.utils._

import scala.collection.mutable
// import scala.reflect.runtime.currentMirror
// import scala.tools.reflect.ToolBox



trait Holder {
  def value(vs: Seq[Any]): Value
}

object ObjRestrict extends ObjWorker {

  var hashSet = new mutable.HashSet[AnyRef]()

  override def supportShallow(v1: AnyRef): Value.SupportShallow = {
    hashSet.clear()
    supportShallow0(v1)
  }

  def supportShallow0(v1: AnyRef): Value.SupportShallow = {
    val clz = v1.getClass
    val fs = clz.getDeclaredFields
    var ns = SupportShallow.empty
    for (f <- fs) {
      f.setAccessible(true)
      val o = f.get(v1)
      o match {
        case v: Value =>
          ns = ns ++ v.supportShallow()
        case f: semantic.Formula =>
          ns = ns +- f.names
        case p: Pattern =>
        case a =>
          if (hashSet.contains(a)) {
            val j = 1
          } else {
            hashSet.add(a)
            ns = ns ++ supportShallow0(a)
          }
      }
    }
    ns
  }

  override def restrict(v1: AnyRef, v2: Assignments): AnyRef = {
    val clz = v1.getClass
    val fs = clz.getDeclaredFields
    val ns = new Array[AnyRef](fs.size)
    val cons = clz.getDeclaredConstructors
    assert(cons.size == 1)
    var changed = false
    var i = 0
    for (f <- fs) {
      f.setAccessible(true)
      val o = f.get(v1)
      o match {
        case v: Value =>
          val r = v.restrict(v2)
          ns(i) = r
          if (!v.eq(r)) changed = true
        case f: semantic.Formula =>
          val r = f.restrict(v2)
          ns(i) = r
          if (!f.eq(r)) changed = true
        case p: Pattern =>
          ns(i) = p
        case a =>
          // this happens because of the code NOT GENERATED in `Value.scala` has more liberate ways of referring things
          restrict(a, v2)
      }
      i += 1
    }
    if (changed) {
      val c = cons(0)
      c.setAccessible(true)
      c.newInstance(ns : _*).asInstanceOf[AnyRef]
    } else {
      v1
    }
  }

}

trait PlatformEvaluator extends Evaluator {

  Value.RESTRICT_OBJ = ObjRestrict

  val REDUCE= ""
  //val REDUCE= ".reduceUntilSelf()"
  
  private def compile[A](string: String): A = Benchmark.HoasCompile {
    // try {
    //   val toolbox = currentMirror.mkToolBox()
    //   val tree = toolbox.parse(string)
    //   toolbox.eval(tree).asInstanceOf[A]
    // } catch {
    //   case e: Throwable => throw PlatformEvaluatorException(string, e)
    // }
    null.asInstanceOf[A]
  }

  private def source(a: Name): String = "Name(\"" + a.main + "\")"

    def emitInner(term: Abstract.MetaEnclosedT, d: Int): String = {
      if (term.metas.isEmpty) {
        emit(term.term, d)
      } else {
        s"{ " +
          (for (r <- 0 until term.metas.size) yield s"val m${d}_$r = Meta(null); ").mkString +
            s"${term.metas.zipWithIndex.map(a =>
              s"m${d}_${a._2}.state = MetaState.Closed(${emit(a._1, d)}); ").mkString("")}" +
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

  def emitMultiClosure(pattern: Pattern, c: Abstract.MultiClosure, depth: Int): String = {
    val (rs, dms) = pattern.atomCount
    val d = depth + 1
    val emit = emitInner(c, d)
    val inner = if (rs == 0 && dms == 0) {
      emit
    } else {
      s"{${(0 until rs).map(i => s"val r${d}_$i = r${d}($i); ").mkString}${(0 until dms).map(i => s"val dm${d}_$i = dm${d}($i); ").mkString}$emit }"
    }
    s"MultiClosure((r$d,dm$d) => $inner)"
  }


    def emitGraph(grf: Abstract.ClosureGraph, depth: Int): String = {
      val d = depth + 1
      def declares(a: String, d: Int, count: Int) =
        (0 until count).map(i => s"val $a${d}_$i = $a${d}($i); ").mkString
      val res = grf.nodes.zipWithIndex.map(pair => {
        val c = pair._1
        val index = pair._2
        val metasBefore = grf.nodes.take(index).map(_.typ.metas.size).sum
        val metaBody =
        s"{ val m$d = m${d}_.asInstanceOf[Seq[Meta]].toBuffer; " +
          s"for (k <- 0 until ${c.typ.metas.size}) { assert(m$d(k + ${metasBefore}) == null); m$d(k + $metasBefore) = Meta(null)}; " +
          declares("m", d, c.typ.metas.size + metasBefore) +
          declares("r", d, index) +
          s"${c.typ.metas.zipWithIndex.map(k => (k._1, k._2 + metasBefore)).map(a => s"m$d(${a._2}).state = MetaState.Closed(${emit(a._1, d)}); ").mkString("")}" +
          s"(m$d.slice($metasBefore, ${metasBefore + c.typ.metas.size}).toSeq, ${emit(c.typ.term, d)})}"
        s"(${c.implicitt}, Seq[Int](${c.deps.mkString(", ")}), ${c.typ.metas.size}, (m${d}_, r$d) => $metaBody)"
      }).mkString(", ")
      val kkk = s"Seq(${grf.restrictions.toSeq.map(a =>
        s"(${emit(a._1, d)}, (m$d: Seq[Value], r$d: Seq[Value]) => {" +
          s" ${declares("m", d, grf.nodes.map(_.typ.metas.size).sum)}" +
          s" ${declares("r", d, grf.nodes.size)}" +
          s" ${emitInner(a._2, d + 1)}" +
          s" })").mkString(", ")}).toMap"
      s"""ClosureGraph.createMetaAnnotated(Seq($res), ${grf.dims}, (dm$d: Seq[Formula]) => { ${declares("dm",d,  grf.dims)} $kkk })""".stripMargin
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
            s"${tunnel(getReference(up - depth - 1, index))}$REDUCE"
          } else {
            if (index == -1) s"r${depth - up}$REDUCE" else s"r${depth - up}_$index$REDUCE"
          }
        case Abstract.MetaReference(up, index) =>
          if (up > depth) {
            s"${tunnel(getMetaReference(up - depth - 1, index))}$REDUCE"
          } else {
            s"m${depth - up}_$index$REDUCE"
          }
        case Abstract.Let(metas, definitions, in) =>
          if (metas.isEmpty && definitions.isEmpty) {
            emit(in, depth + 1)
          } else {
            val d = depth + 1
            s"{ " +
              (for (r <- 0 until definitions.size) yield s"val r${d}_$r = LocalReference(null); ").mkString +
              (for (r <- 0 until metas.size) yield s"val m${d}_$r = Meta(null); ").mkString +
                s"${metas.zipWithIndex.map(a =>
                  s"m${d}_${a._2}.state = MetaState.Closed(${emit(a._1, d)}); ").mkString("")}" +
                s"${definitions.zipWithIndex.map(a =>
                  s"r${d}_${a._2}.value = ${emit(a._1, d)}; ").mkString("")}" +
                s"${emit(in, d)}" +
                s"}"
          }
        case Abstract.Function(domain, impict, codomain) =>
          s"Function(${emit(domain, depth)}, $impict, ${emitClosure(codomain, depth)})"
        case Abstract.Lambda(closure) =>
          s"Lambda(${emitClosure(closure, depth)})"
        case Abstract.App(left, right) =>
          s"App(${emit(left, depth)}, ${emit(right, depth)})$REDUCE"
        case Abstract.Record(id, names, nodes) =>
          s"""Record( ${emit(id, depth)}, Seq(${names.map(n => source(n)).mkString(", ")}), ${emitGraph(nodes, depth)})"""
        case Abstract.Projection(left, field) =>
          s"Projection(${emit(left, depth)}, $field)$REDUCE"
        case Abstract.Sum(id, hit, constructors) =>
          s"""Sum(${emit(id, depth)}, $hit, Seq(${constructors.map(c => emitConstructor(c, depth)).mkString(", ")}))"""
        case Abstract.Make(vs) =>
          s"Make(${vs.map(v => emit(v, depth))})"
        case Abstract.Construct(name, vs, ds, ty) =>
          s"Construct($name, ${vs.map(v => emit(v, depth))}, ${ds.map(d => emit(d, depth))}, ${emitEnclosedSystem(ty, depth)})"
        case Abstract.PatternLambda(id, dom, codomain, cases) =>
          s"PatternLambda($id, ${emit(dom, depth)}, ${emitClosure(codomain, depth)}, Seq(${cases.map(c => s"Case(${tunnel(c.pattern)}, ${emitMultiClosure(c.pattern, c.body, depth)})").mkString(", ")}))"
        case Abstract.PathApp(left, right) =>
          s"PathApp(${emit(left, depth)}, ${emit(right, depth)})$REDUCE"
        case Abstract.PathLambda(body) =>
          s"PathLambda(${emitAbsClosure(body, depth)})"
        case Abstract.PathType(typ, left, right) =>
          s"PathType(${emitAbsClosure(typ, depth)}, ${emit(left, depth)}, ${emit(right, depth)})"
        case Abstract.Transp(tp, dir, base) =>
          s"Transp(${emitAbsClosure(tp, depth)}, ${emit(dir, depth)}, ${emit(base, depth)})$REDUCE"
        case Abstract.Hcomp(tp, base, faces) =>
          s"Hcomp(" +
              s"${emit(tp, depth)}, " +
              s"${emit(base, depth)}, " +
              emitAbsClosureSystem(faces, depth) +
              s")$REDUCE"
        case Abstract.Comp(tp, base, faces) =>
          s"Comp(" +
              s"${emitAbsClosure(tp, depth)}, " +
              s"${emit(base, depth)}, " +
              emitAbsClosureSystem(faces, depth) +
              s")$REDUCE"
        case Abstract.GlueType(tp, faces) =>
          s"GlueType(" +
              s"${emit(tp, depth)}, " +
              emitEnclosedSystem(faces, depth) +
              s")$REDUCE"
        case Abstract.Glue(base, faces) =>
          s"Glue(" +
              s"${emit(base, depth)}, " +
            emitEnclosedSystem(faces, depth) +
              s")$REDUCE"
        case Abstract.Unglue(tp, base, iu, faces) =>
          s"Unglue(" +
              s"${emit(tp, depth)}, " +
              s"${emit(base, depth)}, " + iu + ", " +
            emitEnclosedSystem(faces, depth) +
              s")$REDUCE"
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

  private val vs = mutable.ArrayBuffer[Any]()
  private val ns = mutable.ArrayBuffer[String]()

  protected def extractFromHolder(h: Holder): Value = {
    val res = h.value(vs.toSeq)
    ns.clear()
    vs.clear()
    res
  }

  private def tunnel(v: Any, str: String): String = {
    val i = vs.size
    vs += v
    ns += str
    s"vs$i"
  }

  protected def tunnel(v: semantic.Formula): String = {
    tunnel(v, "Formula")
  }

  protected def tunnel(v: Value): String = {
    tunnel(v, "Value")
  }

  protected def tunnel(v: Pattern): String = {
    tunnel(v, "Pattern")
  }

  private def holderSrc(res: String): String = {

      val defs = (0 until vs.size).map(i => s"val vs${i} = vs($i).asInstanceOf[${ns(i)}]").mkString("\n")
      s"""
         |import mlang.utils._
         |import mlang.compiler._
         |import mlang.compiler.Value._
         |
         |
         |new Holder {
         |  def value(vs: Seq[Any]): Value = {
         |  $defs
         |  val res = $res
         |  res
         |  }
         |}
         |""".stripMargin
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
