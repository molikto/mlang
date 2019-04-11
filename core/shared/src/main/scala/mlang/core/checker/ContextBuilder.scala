package mlang.core.checker

import mlang.core.concrete.{Pattern => Patt}
import mlang.core.Name



sealed trait ContextBuilderException extends CoreException

object ContextBuilderException {

  class AlreadyDeclared() extends ContextBuilderException
  class AlreadyDefined() extends ContextBuilderException
  class NotDeclared() extends ContextBuilderException

}


import Context._

trait ContextBuilder extends Context {

  type Self <: ContextBuilder

  private val gen = GenericGen.Positive

  protected implicit def create(a: Layers): Self


  def newLayer(): Self = (Seq.empty : Layer) +: layers

  def newDeclaration(name: Name, typ: Value) : Self = {
    layers.head.find(_.name.intersect(name)) match {
      case Some(_) => throw new ContextBuilderException.AlreadyDeclared()
      case _ => (layers.head :+ Binder(gen(), name, typ)) +: layers.tail
    }
  }

  def newDefinitionChecked(name: Name, v: Value) : Self = {
    layers.head.find(_.name.intersect(name)) match {
      case Some(Binder(id, _, typ, tv)) => tv match {
        case Some(_) => throw new ContextBuilderException.AlreadyDefined()
        case _ => layers.head.updated(layers.head.indexWhere(_.name.intersect(name)), Binder(id, name, typ, Some(v))) +: layers.tail
      }
      case _ => throw new ContextBuilderException.NotDeclared()
    }
  }

  def newDefinition(name: Name, typ: Value, v: Value): Self = {
    layers.head.find(_.name.intersect(name)) match {
      case Some(_) => throw new ContextBuilderException.AlreadyDeclared()
      case _ => (layers.head :+ Binder(gen(), name, typ, Some(v))) +: layers.tail
    }
  }

  def newAbstraction(name: Name, typ: Value) : (Self, Value) = {
    layers.head.find(_.name.intersect(name)) match {
      case Some(_) => throw new ContextBuilderException.AlreadyDeclared()
      case _ =>
        val g = gen()
        val v = Value.OpenReference(g, typ)
        ((layers.head :+ Binder(g, name, typ, Some(v))) +: layers.tail, v)
    }
  }

  def compile(pattern: Patt): Pattern = {
    def rec(p: Patt): Pattern = {
      p match {
        case Patt.Atom(_) =>
          Pattern.Atom
        case Patt.Make(maps) =>
          Pattern.Make(maps.map(compile))
        case Patt.Constructor(name, maps) =>
          Pattern.Constructor(name, maps.map(compile))
      }
    }
    rec(pattern)
  }

  def names(pattern: Patt): Seq[Name] = {
    def rec(p: Patt): Seq[Name] = {
      p match {
        case Patt.Atom(n) =>
          Seq(n)
        case Patt.Make(maps) =>
          maps.flatMap(names)
        case Patt.Constructor(_, maps) =>
          maps.flatMap(names)
      }
    }
    rec(pattern)
  }


  def newAbstractions(pattern: Patt, typ: Value): (Self, Value) = {
    val ns = names(pattern)
    val (os, v) = Value.extractTypes(compile(pattern), typ, gen)
    assert(os.size == ns.size)
    val ctx: Self = (layers.head ++ os.zip(ns).map(o => Binder(o._1.id, o._2, o._1.typ, Some(o._1)))) +: layers.tail
    (ctx, v)
  }
}
