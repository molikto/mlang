package mlang.core.checker

import mlang.core.concrete.{Pattern => Patt}
import mlang.core.name._

import scala.collection.mutable



sealed trait ContextBuilderException extends CoreException

object ContextBuilderException {

  
  case class AlreadyDeclared() extends ContextBuilderException
  case class AlreadyDefined() extends ContextBuilderException
  case class NotDeclared() extends ContextBuilderException

}


import Context._

trait ContextBuilder extends Context {

  type Self <: ContextBuilder

  private val gen = GenericGen.Positive

  protected implicit def create(a: Layers): Self


  def newLayer(): Self = (Seq.empty : Layer) +: layers

  def newDeclaration(name: Name, typ: Value, genericValue: Boolean) : Self = {
    layers.head.find(_.name.intersect(name)) match {
      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
      case _ =>
        val g = gen()
        (layers.head :+ Binder(g, name, typ, false, if (genericValue) Some(Value.OpenReference(g, typ)) else None)) +: layers.tail
    }
  }

  def newDefinitionChecked(index: Int, name: Name, v: Value) : Self = {
    layers.head(index) match {
      case Binder(id, n0, typ, defined, tv) =>
        if (defined) {
          throw ContextBuilderException.AlreadyDefined()
        } else {
          assert(n0 == name)
          layers.head.updated(index, Binder(id, name, typ, true, Some(v))) +: layers.tail
        }
    }
  }

//  def newDefinition(name: Name, typ: Value, v: Value): Self = {
//    layers.head.find(_.name.intersect(name)) match {
//      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
//      case _ => (layers.head :+ Binder(gen(), name, typ, true, Some(v))) +: layers.tail
//    }
//  }

  def newAbstraction(name: Name, typ: Value) : (Self, Value) = {
    layers.head.find(_.name.intersect(name)) match {
      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
      case _ =>
        val g = gen()
        val v = Value.OpenReference(g, typ)
        ((layers.head :+ Binder(g, name, typ, true, Some(v))) +: layers.tail, v)
    }
  }


  def newAbstractions(pattern: Patt, typ: Value): (Self, Value, Pattern) = {
    val vvv = mutable.ArrayBuffer[Binder]()
    def rec(p: Patt, @canrecur t0: Value): (Value, Pattern) = {
      val t = t0.deRecursiveHead()
      p match {
        case Patt.Atom(name) =>
          var ret: (Value, Pattern) = null
          name.flatMap(_.asRef) match {
            case Some(ref) =>
              t match {
                case Value.Sum(_, cs) if cs.exists(c => c.name == ref && c.parameters == 0) =>
                  ret = (Value.Construct(ref, Seq.empty), Pattern.Construct(ref, Seq.empty))
                case _ =>
              }
            case _ =>
          }
          if (ret == null) {
            val open = Value.OpenReference(gen(), t)
            if (name.isDefined) {
              vvv.append(Binder(gen(), name.get, t, true, Some(open)))
            }
            ret = (open, Pattern.Atom)
          }
          ret
        case Patt.Group(maps) =>
          t match {
            case r@Value.Record(_, nodes) =>
              if (maps.size == nodes.size) {
                var vs =  Seq.empty[(Value, Pattern)]
                for (m  <- maps) {
                  val it = r.projectedType(vs.map(_._1), vs.size)
                  val tv = rec(m, it)
                  vs = vs :+ tv
                }
                (Value.Make(vs.map(_._1)), Pattern.Make(vs.map(_._2)))
              } else {
                throw new PatternExtractException.MakeWrongSize()
              }
            case _ => throw new PatternExtractException.MakeIsNotRecordType()
          }
        case Patt.NamedGroup(name, maps) =>
          t match {
            case Value.Sum(_, cs) =>
              cs.find(_.name == name) match {
                case Some(c) =>
                  if (c.nodes.size == maps.size) {
                    val vs = new mutable.ArrayBuffer[(Value, Pattern)]()
                    for ((m, n) <- maps.zip(c.nodes)) {
                      val it = n(vs.map(_._1))
                      val tv = rec(m, it)
                      vs.append(tv)
                    }
                    (Value.Construct(name, vs.map(_._1)), Pattern.Construct(name, vs.map(_._2)))
                  } else {
                    throw new PatternExtractException.ConstructWrongSize()
                  }
                case _ =>
                  throw new PatternExtractException.ConstructUnknownName()
              }
            case _ => throw new PatternExtractException.ConstructNotSumType()
          }
      }
    }
    val (os, p) = rec(pattern, typ)
    val ctx: Self = (layers.head ++ vvv) +: layers.tail
    (ctx, os, p)
  }
}
