package mlang.compiler

import mlang.compiler.Abstract.Formula

trait DebugPrettyPrinter extends ElaboratorContextBuilder {
  override type Self <: DebugPrettyPrinter


  def print(a: Abstract): Unit = println(debugPPrint(a))

  def debugPPrintInner(ms: Abstract.MetaEnclosedT): String = {
    if (ms.metas.isEmpty) debugPPrint(ms.term) else {
      val sb = new StringBuilder()
      sb.append("{\n")
      val metas = ms.metas
      val ctx = this
      for (m <- metas) ctx.solvedMeta(null)
      for ((m, ii) <- metas.zipWithIndex) {
        val name = ctx.layers.head.metas.metas(ii)._1.main
        sb.append(s"meta $name = ${ctx.debugPPrint(m)}\n")
      }
      sb.append(ctx.debugPPrint(ms.term))
      sb.append("}")
      sb.toString()
    }
  }

  def debugPPrint(ast: Abstract.Formula): String = {
    ast match {
      case Formula.Reference(up) =>
        layers(up) match {
          case d: Layer.Dimension => d.name.main.toString
          case _ => logicError()
        }
      case Formula.True => "1"
      case Formula.False => "0"
      case Formula.And(left, right) => s"and(${debugPPrint(left)}, ${debugPPrint(right)}"
      case Formula.Or(left, right) => s"or(${debugPPrint(left)}, ${debugPPrint(right)}"
      case Formula.Neg(unit) => s"neg(${debugPPrint(unit)})"
    }
  }

  def debugPPrintAbsClosure(ast: Abstract.AbsClosure): String = {
    debugPPrint(Abstract.PathLambda(ast))
  }

  def debugPPrint(ast: Seq[Abstract.Face]): String = {
    ast.map(a => s"| ${a.pair}: ${debugPPrintAbsClosure(a.body)}").mkString("")
  }

  def debugPPrint(ast: Abstract): String = {
    ast match {
      case Abstract.Universe(i) => if (i == 0) "type" else "^" * i + "type"
      case Abstract.Reference(up, index) =>
        (layers(up) match {
          case parameters: Layer.Parameters if index >= 0 => parameters.binders(index).name.main
          case Layer.Parameter(binder, _) if index == -1 => binder.name.main
          case Layer.Defines(_, terms) if index >= 0 => terms(index).typ0.name.main
          case Layer.Defines(_, terms) => terms.head.typ0.name.main
          case whatever => logicError(s"$whatever is unexpected")
        }).toString
      case Abstract.MetaReference(up, index) =>
        s"#${layers(up).metas.metas(index)._1.main}"
      case Abstract.Let(metas, definitions, in) =>
        var ctx = newDefinesLayer().asInstanceOf[DebugPrettyPrinter]
        val sb = new StringBuilder()
        sb.append("run {\n")
        for (m <- metas) ctx.solvedMeta(null)
        for (d <- definitions) ctx = ctx.newDefinition(GenName(), null, null)._1.asInstanceOf[DebugPrettyPrinter]
        for ((m, ii) <- metas.zipWithIndex) {
          val name = ctx.layers.head.metas.metas(ii)._1.main.toString
          sb.append(s"meta $name = ${ctx.debugPPrint(m)}\n")
        }
        for ((d, ii) <- definitions.zipWithIndex) {
          val name = ctx.layers.head.asInstanceOf[Layer.Defines].terms(ii).typ0.name.main.toString
          sb.append(s"define $name = ${ctx.debugPPrint(d)}\n")
        }
        sb.append(ctx.debugPPrint(in))
        sb.append("}")
        sb.toString()
      case Abstract.Function(domain, impict, codomain) =>
        val name = GenName()
        val ctx = newParameterLayer(name, null)._1
        val imp = if (impict) "#" else ""
        s"($imp${name.main}: ${debugPPrint(domain)}) ⇒ ${ctx.debugPPrintInner(codomain)}"
      case Abstract.Lambda(closure) =>
        val name = GenName()
        val ctx = newParameterLayer(name, null)._1
        s"${name.main} → ${ctx.debugPPrintInner(closure)}"
      case Abstract.PathLambda(body) =>
        val name = GenName()
        val ctx = newDimensionLayer(name, null)
        s"${name.main} → ${ctx.debugPPrintInner(body)}"
      case Abstract.PatternLambda(id, domain, typ, cases) =>
        "[pattern lambda]"
      case Abstract.App(left, right) =>
        s"${debugPPrint(left)}(${debugPPrint(right)})"
      case Abstract.Record(inductively, names, implicits, graph) =>
        "[record]"
      case Abstract.Sum(inductively, constructors) =>
        "[sum]"
      case Abstract.Projection(left, field) =>
        s"${debugPPrint(left)}.$field"
      case Abstract.Make(vs) =>
        "make(" + vs.map(a => debugPPrint(a)) + ")"
      case Abstract.Construct(f, vs) =>
        s"construct($f, " + vs.map(a => debugPPrint(a)) + ")"
      case Abstract.PathType(typ, left, right) =>
        s"path(${debugPPrint(left)}, ${debugPPrintAbsClosure(typ)}, ${debugPPrint(right)})"
      case Abstract.PathApp(let, r) =>
        s"${debugPPrint(let)}@(${debugPPrint(r)})"
      case Abstract.Transp(tp, direction, base) =>
        s"transp(${debugPPrintAbsClosure(tp)}, ${debugPPrint(direction)}, ${debugPPrint(base)})"
      case Abstract.Hcomp(tp, base, faces) =>
        s"hcomp(${debugPPrint(tp)}, ${debugPPrint(base)} ${debugPPrint(faces)})"
      case Abstract.Comp(tp, base, faces) =>
        s"hcomp(${debugPPrintAbsClosure(tp)}, ${debugPPrint(base)} ${debugPPrint(faces)})"
      case Abstract.GlueType(tp, faces) =>
        s"glue_type(${debugPPrint(tp)} ${debugPPrint(faces)})"
      case Abstract.Glue(base, faces) =>
        s"glue(${debugPPrint(base)} ${debugPPrint(faces)})"
      case Abstract.Unglue(tp, base, faces) =>
        s"glue(${debugPPrint(tp)}, ${debugPPrint(base)} ${debugPPrint(faces)})"
    }
  }
}
