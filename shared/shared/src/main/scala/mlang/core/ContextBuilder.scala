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



  protected def createMetas(): Metas = mutable.ArrayBuffer.empty[Unit]




  def newRestrictionLayer(pair: Value.DimensionPair): Self = {
    Layer.Restriction(pair, createMetas()) +: layers
  }




  def newDimensionLayer(n: Name): (Self, Value.Dimension) = {
    val l = Layer.Dimension(dgen(), n, createMetas())
    val ctx: Self = l +: layers
    (ctx, l.value)
  }



  def debug__headDefinesSize = layers.head.asInstanceOf[Layer.Defines].terms.size

  def getDefined(i: Int): (Value, Option[Value]) = layers.head match {
    case Layer.Defines(_, defines) =>
      val ds = defines(i)
      (ds.typ, ds.v)
    case _ => logicError()
  }

  def lookupDefined(a: Name): Option[(Int, Value, Option[Value])] = layers.head match {
    case Layer.Defines(_, defines) =>
      val index = defines.indexWhere(_.name.intersect(a))
      if (index < 0) {
        None
      } else {
        val ds = defines(index)
        Some((index, ds.typ, ds.v))
      }
    case _ => logicError()
  }

  def newDefinesLayer(): Self = Layer.Defines(createMetas(), Seq.empty) +: layers

  def newDefinition(name: Name, typ: Value, v: Value) : Self = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines.find(_.name.intersect(name)) match {
          case Some(_) => throw ContextBuilderException.AlreadyDeclared()
          case _ =>
            val g = gen()
            Layer.Defines(metas, defines :+ DefineItem(ParameterBinder(g, name, typ), Some(v))) +: layers.tail
        }
      case _ => logicError()
    }
  }

  def newDefinitionChecked(index: Int, name: Name, v: Value) : Self = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines(index) match {
          case d@DefineItem(typ0, v0) =>
            assert(d.name == name)
            assert(v0.isEmpty)
            Layer.Defines(metas, defines.updated(index, DefineItem(typ0, Some(v)))) +: layers.tail
          case _ =>
            throw ContextBuilderException.AlreadyDefined()
        }
      case _ => logicError()
    }
  }

  def newDeclaration(name: Name, typ: Value) : Self = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines.find(_.name.intersect(name)) match {
          case Some(_) => throw ContextBuilderException.AlreadyDeclared()
          case _ =>
            val g = gen()
            Layer.Defines(metas, defines :+ DefineItem(ParameterBinder(g, name, typ), None)) +: layers.tail
        }
      case _ => logicError()
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
    (Layer.Parameter(binder, createMetas()) +: layers, binder.value)
  }





  def newParametersLayer(): Self = Layer.ParameterGraph(Seq.empty, createMetas()) +: layers


  def newParameter(name: Name, typ: Value) : (Self, Value) = {
    layers.head match {
      case Layer.ParameterGraph(binders, metas) =>
        binders.find(_.t.name.intersect(name)) match {
          case Some(_) => throw ContextBuilderException.AlreadyDeclared()
          case _ =>
            val g = gen()
            val v = Value.Generic(g, typ)
            (Layer.ParameterGraph(
              binders :+ MetaEnclosed[ParameterBinder](metas, ParameterBinder(g, name, typ)), createMetas()) +: layers.tail, v)
        }
      case _ => logicError()
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
    val ctx: Self = Layer.MultiParameters(vvv, createMetas()) +: layers
    (ctx, os, p)
  }
}
