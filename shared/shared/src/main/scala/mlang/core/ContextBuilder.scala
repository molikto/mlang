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
  private val gen =new LongGen.Positive()
  private val dgen = new LongGen.Positive()
}

import ContextBuilder._

trait ContextBuilder extends Context {

  type Self <: ContextBuilder

  protected implicit def create(a: Layers): Self


  def newParametersLayer(): Self = Layer.Parameters(Seq.empty) +: layers

  def newDefinesLayer(): Self = Layer.Defines(Seq.empty) +: layers

  def newRestrictionLayer(pair: Value.DimensionPair): Self = {
    Layer.Restriction(pair) +: layers
  }

  def newDimensionLayer(n: Name): (Self, Value.Dimension) = {
    val l = Layer.Dimension(dgen(), n)
    val ctx: Self = l +: layers
    (ctx, l.value)
  }

  protected def headDefines: Seq[DefineBinder] = layers.head.asInstanceOf[Layer.Defines].terms
  protected def headParams: Seq[ParameterBinder] = layers.head.asInstanceOf[Layer.Parameters].terms

  def newDefinition(name: Name, typ: Value, v: Value) : Self = {
    headDefines.find(_.name.intersect(name)) match {
      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
      case _ =>
        val g = gen()
        Layer.Defines(headDefines :+ DefineBinder(g, name, typ, Some(v))) +: layers.tail
    }
  }

  def newDefinitionChecked(index: Int, name: Name, v: Value) : Self = {
    headDefines(index) match {
      case DefineBinder(id, n0, typ, None) =>
        assert(n0 == name)
        Layer.Defines(headDefines.updated(index, DefineBinder(id, name, typ, Some(v)))) +: layers.tail
      case _ =>
        throw ContextBuilderException.AlreadyDefined()
    }
  }

  def newDeclaration(name: Name, typ: Value) : Self = {
    headDefines.find(_.name.intersect(name)) match {
      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
      case _ =>
        Layer.Defines(headDefines :+ DefineBinder(gen(), name, typ, None)) +: layers.tail
    }
  }


//  def newDefinition(name: Name, typ: Value, v: Value): Self = {
//    layers.head.find(_.name.intersect(name)) match {
//      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
//      case _ => (layers.head :+ Binder(gen(), name, typ, true, Some(v))) +: layers.tail
//    }
//  }

  def newParameterLayer(name: Name, typ: Value): (Self, Value) = {
    val binder = ParameterBinder(gen(), name, typ)
    (Layer.Parameter(binder) +: layers, binder.value)
  }

  def newParameter(name: Name, typ: Value) : (Self, Value) = {
    headParams.find(_.name.intersect(name)) match {
      case Some(_) => throw ContextBuilderException.AlreadyDeclared()
      case _ =>
        val g = gen()
        val v = Value.Generic(g, typ)
        (Layer.Parameters(headParams :+ ParameterBinder(g, name, typ)) +: layers.tail, v)
    }
  }

  def newPatternLayer(pattern: Patt, typ: Value): (Self, Value, Pattern) = {
    val vvv = mutable.ArrayBuffer[ParameterBinder]()
    def rec(p: Patt, t: Value): (Value, Pattern) = {
      p match {
        case Patt.Atom(name) =>
          var ret: (Value, Pattern) = null
          name.asRef match {
            case Some(ref) =>
              t.whnf match {
                case Value.Sum(_, cs) if cs.exists(c => c.name == ref && c.parameters == 0) =>
                  ret = (Value.Construct(ref, Seq.empty), Pattern.Construct(ref, Seq.empty))
                case _ =>
              }
            case _ =>
          }
          if (ret == null) {
            val open = ParameterBinder(gen(), name, t)
            vvv.append(open)
            ret = (open.value, Pattern.Atom)
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
    val ctx: Self = Layer.Parameters(vvv) +: layers
    (ctx, os, p)
  }
}
