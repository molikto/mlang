package mlang.core

import mlang.concrete.{Pattern => Patt}
import mlang.core
import mlang.core.Value.ClosureGraph
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

trait ContextBuilder extends ContextWithMetaOps {

  type Self <: ContextBuilder

  protected implicit def create(a: Layers): Self


  def drop(up: Int): Self = {
    create(layers.drop(up))
  }

  def newRestrictionLayer(pair: Value.DimensionPair): Self = {
    Layer.Restriction(pair, createMetas()) +: layers
  }




  def newDimensionLayer(n: Name, dimension: Option[Long] = None): (Self, Value.Dimension.Generic) = {
    val l = Layer.Dimension(dimension.getOrElse(dgen()), n, createMetas())
    val ctx: Self = l +: layers
    (ctx, l.value)
  }



  def lookupDefined(a: Name): Option[(Int, Value)] = layers.head match {
    case Layer.Defines(_, defines) =>
      val index = defines.indexWhere(_.name.intersect(a))
      if (index < 0) {
        None
      } else {
        val ds = defines(index)
        Some((index, ds.typ))
      }
    case _ => logicError()
  }

  def newDefinesLayer(): Self = Layer.Defines(createMetas(), Seq.empty) +: layers

  def newDefinition(name: Name, typ: Value, v: Value.Reference) : (Self, Int, Value.Generic) = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines.find(_.name.intersect(name)) match {
          case Some(_) => throw ContextBuilderException.AlreadyDeclared()
          case _ =>
            val g = Value.Generic(gen(), typ)
            (Layer.Defines(metas, defines :+ DefineItem(ParameterBinder(name, g), Some(v))) +: layers.tail, defines.size, g)
        }
      case _ => logicError()
    }
  }


  def newDefinitionChecked(index: Int, name: Name, v: Value.Reference) : Self = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines(index) match {
          case DefineItem(typ0, None) =>
            assert(typ0.name == name)
            Layer.Defines(metas, defines.updated(index, DefineItem(typ0, Some(v)))) +: layers.tail
          case _ =>
            throw ContextBuilderException.AlreadyDefined()
        }
      case _ => logicError()
    }
  }

  def newDeclaration(name: Name, typ: Value) : (Self, Int, Value.Generic) = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines.find(_.name.intersect(name)) match {
          case Some(_) => throw ContextBuilderException.AlreadyDeclared()
          case _ =>
            val g = Value.Generic(gen(), typ)
            val p = ParameterBinder(name, g)
            (Layer.Defines(metas, defines :+ DefineItem(p, None)) +: layers.tail, defines.size, g)
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
    val g = Value.Generic(gen(), typ)
    (Layer.Parameter(ParameterBinder(name, g), createMetas()) +: layers, g)
  }

  def newParameterLayerProvided(name: Name, g: Value.Generic): Self = {
    Layer.Parameter(ParameterBinder(name, g), createMetas()) +: layers
  }





  def newParametersLayer(): Self = Layer.ParameterGraph(Seq.empty, createMetas()) +: layers


  def newParameter(name: Name, typ: Value) : (Self, Value) = {
    layers.head match {
      case Layer.ParameterGraph(binders, metas) =>
        binders.find(_.name.intersect(name)) match {
          case Some(_) => throw ContextBuilderException.AlreadyDeclared()
          case _ =>
            val g = gen()
            val v = Value.Generic(g, typ)
            assert(metas.debug_allFrozen)
            (Layer.ParameterGraph(
              binders :+ ParameterBinder(name, v), metas) +: layers.tail, v)
        }
      case _ => logicError()
    }
  }





  def newPatternLayer(pattern: Patt, typ: Value): (Self, Value, Pattern) = {
    val vvv = mutable.ArrayBuffer[ParameterBinder]()
    def recs(maps: Seq[Patt], nodes: ClosureGraph): Seq[(Value, Pattern)] = {
      var vs =  Seq.empty[(Value, Pattern)]
      var graph = nodes
      for (i <- maps.indices) {
        val tv = rec(maps(i), graph(i).independent.typ)
        graph = ClosureGraph.reduce(graph, vs.size, tv._1)
        vs = vs :+ tv
      }
      vs
    }

    def rec(p: Patt, t: Value): (Value, Pattern) = {
      p match {
        case Patt.Atom(name) =>
          var ret: (Value, Pattern) = null
          var indexaa = 0
          name.asRef match {
            case Some(ref) =>
              t.whnf match {
                case Value.Sum(_, cs) if { indexaa = cs.indexWhere(c => c.name.by(ref) && c.nodes.isEmpty); indexaa >= 0 } =>
                  ret = (Value.Construct(indexaa, Seq.empty), Pattern.Construct(indexaa, Seq.empty))
                case _ =>
              }
            case _ =>
          }
          if (ret == null) {
            val open = ParameterBinder(name, Value.Generic(gen(), t))
            vvv.append(open)
            ret = (open.value, Pattern.Atom)
          }
          ret
        case Patt.Group(maps) =>
          t.whnf match {
            case r: Value.Record =>
              if (maps.size == r.nodes.size) {
                val vs = recs(maps, r.nodes)
                (Value.Make(vs.map(_._1)), Pattern.Make(vs.map(_._2)))
              } else {
                throw PatternExtractException.MakeWrongSize()
              }
            case _ => throw PatternExtractException.MakeIsNotRecordType()
          }
        case Patt.NamedGroup(name, maps) =>
          t.whnf match {
            case Value.Sum(_, cs) =>
              val index = cs.indexWhere(_.name.by(name))
              if (index >= 0) {
                val c = cs(index)
                if (c.nodes.size == maps.size) {
                  val vs = recs(maps, c.nodes)
                  (Value.Construct(index, vs.map(_._1)), Pattern.Construct(index, vs.map(_._2)))
                } else {
                  throw PatternExtractException.ConstructWrongSize()
                }
              } else {
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
