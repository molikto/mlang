package c_elaborator

import a_core.{Context, _}
import b_surface_syntax.surface

import scala.collection.mutable


sealed trait ContextLayer {
  def contains(t: String): Boolean
}

case class DeclarationLayer(definitions: Set[String]) extends ContextLayer {
  override def contains(t: String): Boolean = definitions.contains(t)
}
case class LambdaLayer(name: String) extends ContextLayer {
  override def contains(t: String): Boolean = t == name
}

trait Elaborator {

  def flatten(tele: surface.Tele): Seq[(String, surface.Term)] = {
    tele.flatMap(a => a._1.map(n => (n, a._2)))
  }

  def elaborateMaybePi(tele: Option[surface.Tele], body: surface.Term, context: Seq[ContextLayer]): Term = {
    tele match {
      case Some(tele) =>
        val ts = flatten(tele)
        val cx = ts.reverse.map(a => LambdaLayer(a._1)) ++ context
        val bd = elaborate(body, context)
        val tt = ts.foldRight((cx, bd)) { (ps, tm) =>
          val c = tm._1.tail
          (c, Pi(elaborate(ps._2, c), tm._2))
        }
        assert(tt._1.isEmpty)
        tt._2
      case None =>
        elaborate(body, context)
    }
  }

  def elaborateApp(left: surface.Term, ps: Seq[surface.Term], ctx: Seq[ContextLayer]): Term = {
    ps.foldLeft(elaborate(left, ctx)) { (v, p) =>
      Application(v, elaborate(p, ctx))
    }
  }

  def elaborateMaybeLambda(tele: Option[surface.Tele], body: surface.Term, context: Seq[ContextLayer]): Term = {
    // TODO use meta variable instead, checking is faster than infer?
    tele match {
      case Some(tele) =>
        val ts = flatten(tele)
        val cx = ts.reverse.map(a => LambdaLayer(a._1)) ++ context
        val bd = elaborate(body, context)
        val tt = ts.foldRight((cx, bd)) { (ps, tm) =>
          val c = tm._1.tail
          (c, Lambda(elaborate(ps._2, c), tm._2))
        }
        assert(tt._1.isEmpty)
        tt._2
      case None =>
        elaborate(body, context)
    }
  }


  def elaborate(a: surface.Definition, context: Seq[ContextLayer]): Seq[Declaration] = {
    a.ty.toSeq.flatMap(t => {
      Seq(TypeDeclaration(a.name, elaborateMaybePi(a.tele, t, context)))
    }) ++ a.term.toSeq.flatMap(term => {
      Seq(ValueDeclaration(a.name, elaborateMaybeLambda(a.tele, term, context)))
    })
  }

  def elaborate(term: surface.Term, context: Seq[ContextLayer]): Term = {

    def ascript(a: Term, ty: surface.Term): Term = {
      Cast(a, elaborate(ty, context))
    }
    term match {
      case surface.Definitions(defs) =>
        val ctx = DeclarationLayer(defs.map(_.name).toSet) +: context
        Make(defs.flatMap(d => elaborate(d, ctx )))
      case surface.Let(defs, body) =>
        val ctx = DeclarationLayer(defs.map(_.name).toSet) +: context
        val name = surface.letId
        Projection(Make(defs.flatMap(d => elaborate(d, ctx)) ++ elaborate(surface.Definition(name, None, None, Some(body)), ctx)), name)
      case surface.Pi(seq, body) =>
        elaborateMaybePi(Some(seq), body, context)
      case surface.Lambda(seq, body) =>
        elaborateMaybeLambda(Some(seq), body, context)
      case surface.App(left, right) =>
        elaborateApp(left, right, context)
      case surface.Projection(term, str) =>
        Projection(elaborate(term, context), str)
      case surface.Record(seq) =>
        val ctx = DeclarationLayer(seq.map(_._1).toSet) +: context
        Record(seq.map(d => TypeDeclaration(d._1, elaborate(d._2, ctx))))
      case surface.Make(term, seq) =>
        val ctx = DeclarationLayer(seq.map(_._1).toSet) +: context
        val m = Make(seq.map(d => ValueDeclaration(d._1, elaborate(d._2, ctx))))
        ascript(m, term)
      case surface.Ascription(term, right) =>
        ascript(elaborate(term, context), right)
      case surface.Sum(ts) =>
        Sum(ts.map(a => Constructor(a._1, elaborate(a._2, context))))
      case surface.Construct(ty, name, v) =>
        ascript(Construct(name, elaborate(v, context)), ty)
      case surface.Split(t, ts) =>
        Split(elaborate(t, context), ts.map(a => Branch(a._1, elaborate(a._3, LambdaLayer(a._2) +: context))))
      case surface.Primitive(p) =>
        Primitive(p)
      case surface.Reference(t) =>
        context.zipWithIndex.collectFirst {
          case (a, i) if a.contains(t) =>
            a match {
              case LambdaLayer(_) => VariableReference(i)
              case DeclarationLayer(definitions) => DeclarationReference(i, t)
            }
        }.get
      case surface.Absent => ??? // TODO handle lambda without parameter type
    }
  }

  def elaborate(a: surface.Definitions): Make = {
    elaborate(a, Seq.empty).asInstanceOf[Make]
  }
}
