package mlang.core

import mlang.concrete.{Pattern => Patt}
import mlang.name._

import scala.collection.mutable



sealed trait ContextBuilderException extends CoreException

object ContextBuilderException {

  
  case class AlreadyDeclared() extends ContextBuilderException
  case class AlreadyDefined() extends ContextBuilderException
  case class NotDeclared() extends ContextBuilderException

}


import Context._


object ContextBuilder {
  private val gen =new GenericGen.Positive()
  private val dgen = new GenericGen.Positive()
}

import ContextBuilder._

trait ContextBuilder extends Context {

  type Self <: ContextBuilder

  protected implicit def create(a: Layers): Self


  def newTermsLayer(): Self = Layer.Terms(Seq.empty) +: layers

  def newRestrictionLayer(pair: Value.DimensionPair): Option[Self] = {
    pair match {
      case Value.DimensionPair(Value.Dimension.Constant(a), Value.Dimension.Constant(b)) if a != b =>
        None
      case _ =>
        Some(Layer.Restriction(pair) +: layers)
    }
  }

  def newDimensionLayer(n: Name): (Self, Value.Dimension) = {
    val gen = dgen()
    val v = Value.Dimension.OpenReference(gen)
    val ctx: Self = Layer.Dimension(gen, n, v) +: layers
    (ctx, v)
  }

  def newDimensionLayer(n: Name, v: Value.Dimension): Self = {
    val gen = dgen()
    Layer.Dimension(gen, n, v) +: layers
  }

  protected def headTerms: Seq[Binder] = layers.head.asInstanceOf[Layer.Terms].terms

  def newDefinition(name: Name, typ: Value, v: Value) : Self = {
    headTerms.find(_.name.intersect(name)) match {
      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
      case _ =>
        val g = gen()
        Layer.Terms(headTerms :+ Binder(g, name, typ, false, false, v)) +: layers.tail
    }
  }

  def newDefinitionChecked(index: Int, name: Name, v: Value) : Self = {
    headTerms(index) match {
      case Binder(id, n0, typ, defined, _, _) =>
        if (defined) {
          throw ContextBuilderException.AlreadyDefined()
        } else {
          assert(n0 == name)
          Layer.Terms(headTerms.updated(index, Binder(id, name, typ, true, false, v))) +: layers.tail
        }
    }
  }

  def newDeclaration(name: Name, typ: Value) : Self = {
    headTerms.find(_.name.intersect(name)) match {
      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
      case _ =>
        val g = gen()
        Layer.Terms(headTerms :+ Binder(g, name, typ, false, false, Value.OpenReference(g, typ))) +: layers.tail
    }
  }


//  def newDefinition(name: Name, typ: Value, v: Value): Self = {
//    layers.head.find(_.name.intersect(name)) match {
//      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
//      case _ => (layers.head :+ Binder(gen(), name, typ, true, Some(v))) +: layers.tail
//    }
//  }

  def newTermLayer(name: Name, typ: Value): (Self, Value) = {
    val g = gen()
    val v = Value.OpenReference(g, typ)
    (Layer.Term(Binder(g, name, typ, true, true, v)) +: layers, v)
  }

  def newAbstraction(name: Name, typ: Value) : (Self, Value) = {
    headTerms.find(_.name.intersect(name)) match {
      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
      case _ =>
        val g = gen()
        val v = Value.OpenReference(g, typ)
        (Layer.Terms(headTerms :+ Binder(g, name, typ, true, true, v)) +: layers.tail, v)
    }
  }

  def newAbstractionsLayer(pattern: Patt, typ: Value): (Self, Value, Pattern) = {
    val vvv = mutable.ArrayBuffer[Binder]()
    def rec(p: Patt, t: Value): (Value, Pattern) = {
      p match {
        case Patt.Atom(name) =>
          var ret: (Value, Pattern) = null
          name.flatMap(_.asRef) match {
            case Some(ref) =>
              t.whnf match {
                case Value.Sum(_, cs) if cs.exists(c => c.name == ref && c.parameters == 0) =>
                  ret = (Value.Construct(ref, Seq.empty), Pattern.Construct(ref, Seq.empty))
                case _ =>
              }
            case _ =>
          }
          if (ret == null) {
            val open = Value.OpenReference(gen(), t)
            if (name.isDefined) {
              vvv.append(Binder(gen(), name.get, t, true, true, open))
            }
            ret = (open, Pattern.Atom)
          }
          ret
        case Patt.Group(maps) =>
          t.whnf match {
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
                throw PatternExtractException.MakeWrongSize()
              }
            case _ => throw PatternExtractException.MakeIsNotRecordType()
          }
        case Patt.NamedGroup(name, maps) =>
          t.whnf match {
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
                    throw PatternExtractException.ConstructWrongSize()
                  }
                case _ =>
                  throw PatternExtractException.ConstructUnknownName()
              }
            case _ => throw PatternExtractException.ConstructNotSumType()
          }
      }
    }
    val (os, p) = rec(pattern, typ)
    val ctx: Self = Layer.Terms(vvv) +: layers
    (ctx, os, p)
  }
}
