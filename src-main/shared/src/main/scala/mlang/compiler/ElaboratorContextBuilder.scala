package mlang.compiler

import mlang.compiler.Layer.{AlternativeGraph, HitDefinition, Layers}
import mlang.utils.{Name, debug}

import scala.collection.mutable



sealed trait ElaboratorContextBuilderException extends CompilerException

object ElaboratorContextBuilderException {

  
}



object ElaboratorContextBuilder {
  private val gen = new GenLong.Positive()
  private val dgen = new GenLong.Positive()
}

import ElaboratorContextBuilder._

trait ElaboratorContextBuilder extends ElaboratorContextWithMetaOps {

  type Self <: ElaboratorContextBuilder

  protected implicit def create(a: Layers): Self

  def drop(up: Int): Self = create(layers.drop(up))

  def newSyntaxDirectedRestrictionLayer(pair: Value.Formula.Assignments): Self = {
    debug(s"new syntax directed layer $pair")
    Layer.Restriction(0, pair, createMetas()) +: layers
  }

  def newReifierRestrictionLayer(pair: Value.Formula): Self = {
    Layer.ReifierRestriction(createMetas()) +: layers
  }

  def newDimensionLayer(n: Name, dimension: Value.Formula.Generic): Self = {
    val l = Layer.Dimension(DimensionBinder(n, dimension), createMetas())
    val ctx: Self = l +: layers
    ctx
  }

  def newDimensionLayer(n: Name): (Self, Value.Formula.Generic) = {
    val v = Value.Formula.Generic(dgen())
    val l = Layer.Dimension(DimensionBinder(n, v), createMetas())
    val ctx: Self = l +: layers
    (ctx, v)
  }

  def lookupDefined(a: Name): Option[(Int, DefineItem)] = layers.head match {
    case Layer.Defines(_, defines) =>
      val index = defines.indexWhere(_.name.intersect(a))
      if (index < 0) {
        None
      } else {
        val ds = defines(index)
        Some((index, ds))
      }
    case _ => logicError()
  }

  def newDefinesLayer(): Self = Layer.Defines(createMetas(), Seq.empty) +: layers

  def newDefinition(name: Name, typ: Value, v: Value.Reference) : (Self, Int, Value.Generic) = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines.find(_.name.intersect(name)) match {
          case Some(_) => logicError()
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
            logicError()
        }
      case _ => logicError()
    }
  }

  def newDeclaration(name: Name, typ: Value) : (Self, Int, Value.Generic) = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines.find(_.name.intersect(name)) match {
          case Some(_) => logicError()
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




  def newParametersLayer(hit: Option[Value] = None): Self =
    Layer.ParameterGraph(hit.map(a => HitDefinition(a, Seq.empty)), Seq.empty, Seq.empty, createMetas()) +: layers

  def newConstructor(name: Name, ps: Value.ClosureGraph, dim: Int): Self =
    layers.head match {
      case Layer.ParameterGraph(alters,_, _, metas) =>
        alters match {
          case None => logicError()
          case Some(value) =>
            value.branches.find(_.name.intersect(name)) match {
              case Some(_) => logicError()
              case None =>
                assert(metas.debug_allFrozen)
                val n = AlternativeGraph(name, ps, dim)
                Layer.ParameterGraph(Some(HitDefinition(value.self, value.branches :+ n)),  Seq.empty, Seq.empty, createMetas()) +: layers.tail
            }
        }
      case _ => logicError()
    }

  def newParameter(name: Name, typ: Value) : (Self, Value) = {
    layers.head match {
      case Layer.ParameterGraph(alters, binders, ds, metas) =>
        binders.find(_.name.intersect(name)) match {
          case Some(_) => logicError()
          case _ =>
            val g = gen()
            val v = Value.Generic(g, typ)
            assert(metas.debug_allFrozen)
            (Layer.ParameterGraph(alters, binders :+ ParameterBinder(name, v), ds, metas) +: layers.tail, v)
        }
      case _ => logicError()
    }
  }

  def newDimension(name: Name): (Self, Value.Formula.Generic) = {
    layers.head match {
      case Layer.ParameterGraph(alters, binders, ds, metas) =>
        binders.find(_.name.intersect(name)) match {
          case Some(_) => logicError()
          case _ =>
            val v = Value.Formula.Generic(dgen())
            assert(metas.debug_allFrozen)

            (Layer.ParameterGraph(alters, binders, ds :+ DimensionBinder(name, v), metas) +: layers.tail, v)
        }
      case _ => logicError()
    }
  }



  def newPatternLayer(pattern: Concrete.Pattern, typ: Value): (Self, Value, Pattern) = {
    val vvv = mutable.ArrayBuffer[Binder]()
    def recs(maps: Seq[Concrete.Pattern], nodes: Value.ClosureGraph): Seq[(Value, Pattern)] = {
      var vs =  Seq.empty[(Value, Pattern)]
      var graph = nodes
      for (i <- maps.indices) {
        val tv = rec(maps(i), graph(i).independent.typ)
        graph = Value.ClosureGraph.reduce(graph, vs.size, tv._1)
        vs = vs :+ tv
      }
      vs
    }

    def rec(p: Concrete.Pattern, t: Value): (Value, Pattern) = {
      p match {
        case Concrete.Pattern.Atom(name) =>
          var ret: (Value, Pattern) = null
          var index = 0
          name.asRef match { // we make it as a reference here
            case Some(ref) =>
              t.whnf match {
                case sum: Value.Sum if { index = sum.constructors.indexWhere(c => c.name.by(ref) && c.nodes.isEmpty); index >= 0 } =>
                  ret = (Value.Construct(index, Seq.empty, Seq.empty), Pattern.Construct(index, Seq.empty))
                case _ =>
              }
            case _ =>
          }
          if (ret == null) {
            val open = ParameterBinder(name, Value.Generic(gen(), t))
            vvv.append(open)
            ret = (open.value, Pattern.GenericValue)
          }
          ret
        case Concrete.Pattern.Group(maps) =>
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
        case Concrete.Pattern.NamedGroup(name, maps) =>
          t.whnf match {
            case sum: Value.Sum =>
              val index = sum.constructors.indexWhere(_.name.by(name))
              if (index >= 0) {
                val c = sum.constructors(index)
                if (c.nodes.size + c.dim == maps.size) {
                  val vs = recs(maps.take(c.nodes.size), c.nodes)
                  val dPs = maps.drop(c.nodes.size)
                  if (!dPs.forall(_.isInstanceOf[Concrete.Pattern.Atom])) {
                    throw PatternExtractException.NonAtomicPatternForDimension()
                  }
                  val names = dPs.map(_.asInstanceOf[Concrete.Pattern.Atom].id)
                  val ds = names.map(n => DimensionBinder(n, Value.Formula.Generic(dgen())))
                  vvv.appendAll(ds)
                  (Value.Construct(index, vs.map(_._1), ds.map(_.value)), Pattern.Construct(index, vs.map(_._2)))
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
    val ctx: Self = Layer.PatternParameters(vvv.toSeq, createMetas()) +: layers
    (ctx, os, p)
  }
}
