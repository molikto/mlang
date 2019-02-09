package c_elaborator

import a_core._
import b_surface_syntax.surface

import scala.collection.mutable


sealed trait ContextLayer

case class DeclarationLayer(definitions: Set[String]) extends ContextLayer
case class LambdaLayer(name: String) extends ContextLayer

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

    term match {
      case surface.Definitions(defs) =>
        Make(defs.flatMap(d => elaborate(d, DeclarationLayer(defs.map(_.name).toSet) +: context)))
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

      case surface.Make(term, seq) =>
      case surface.Ascription(term, right) =>

      case surface.Sum(ts) =>
      case surface.Construct(ty, name, v) =>
      case surface.Split(term, right) =>
      case surface.Reference(t) =>
      case surface.Absent =>
    }
  }

  def elaborate(a: surface.Definitions): Make = {
    elaborate(a, Seq.empty).asInstanceOf[Make]
  }
}
