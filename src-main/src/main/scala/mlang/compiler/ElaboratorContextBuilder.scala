package mlang.compiler

import mlang.compiler.Layer.{AlternativeGraph, HitDefinition, Layers}
import mlang.utils._
import mlang.compiler.semantic.Value
import mlang.compiler.dbi.given

import scala.collection.mutable



sealed trait ElaboratorContextBuilderException extends CompilerException

object ElaboratorContextBuilderException



object ElaboratorContextBuilder {
  val gen = new GenLong.Positive()
  val dgen = new GenLong.Positive()
}

import ElaboratorContextBuilder._

trait ElaboratorContextBuilder extends ElaboratorContextWithMetaOps {

  type Self <: ElaboratorContextBuilder

  protected implicit def create(a: Layers): Self

  def drop(up: Int): Self = create(layers.drop(up))

  def newSyntaxDirectedRestrictionLayer(pair: semantic.Assignments): Self = {
    debug(s"new syntax directed layer $pair")
    Layer.Restriction(0, pair, createMetas()) +: layers
  }

  def newReifierRestrictionLayer(pair: semantic.Formula): Self = {
    Layer.ReifierRestriction(createMetas()) +: layers
  }

  def newDimensionLayer(n: Name, dimension: semantic.Formula.Generic): Self = {
    val l = Layer.Dimension(DimensionBinder(n, dimension), createMetas())
    val ctx: Self = l +: layers
    ctx
  }

  def newDimensionLayer(n: Name): (Self, semantic.Formula.Generic) = {
    val v = semantic.Formula.Generic(dgen())
    val l = Layer.Dimension(DimensionBinder(n, v), createMetas())
    val ctx: Self = l +: layers
    (ctx, v)
  }

  def newDefinesLayer(): Self = Layer.Defines(createMetas(), Seq.empty) +: layers


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


  def isGlobal = layers.size == 1
  private def newDeclaredGeneric(typ: dbi.Abstract): Leveled[Value.Generic] = {
    val id = gen()
    if (isGlobal) {
      Leveled.Floating(
        Value.Generic(id, evalHack.eval(typ)),
        () => Value.Generic(id, null),
        (ev, i) => ev.eval(typ.lup(0, i)),
        (g, a) => g.initialize(a)
      )
    } else {
      Leveled.Fix(Value.Generic(id, evalHack.eval(typ)))
    }
  }

  private def createGlobalFloating(base: Value.Reference, code: dbi.Abstract): Leveled[Value.Reference] = {
    Leveled.Floating(
      base,
      () => Value.GlobalReference(null),
      (ev, i) => ev.eval(code.lup(0, i)),
      (g, a) => g.value = a
    )
  }

  private def newReference(code: dbi.Abstract, name: Name = null): Leveled[Value.Reference] = {
    if (isGlobal) {
      createGlobalFloating(Value.GlobalReference(evalHack.eval(code)), code)
    } else {
      Leveled.Fix(Value.LocalReference(evalHack.eval(code)))
    }
  }

  // give a definition with body
  def newDefinition(name: Name, typ: dbi.Abstract, code: dbi.Abstract) : (Self, Int, Value.Generic) = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines.find(_.name.intersect(name)) match {
          case Some(_) => logicError()
          case _ =>
            val g = newDeclaredGeneric(typ)
            val r = newReference(code)
            (Layer.Defines(metas, defines :+ DefineItem(ParameterBinder(name, g), typ, r, code)) +: layers.tail, defines.size, g.base)
        }
      case _ => logicError()
    }
  }

  // declare first, used possiblely by a recursive definition, or declaration only, which then used by other recursive definitions
  def newDeclaration(name: Name, typ: dbi.Abstract, isAxiom: Boolean = false) : (Self, Int, Value.Generic) = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines.find(_.name.intersect(name)) match {
          case Some(_) => logicError()
          case _ =>
            if (isAxiom && layers.size != 1) logicError()
            val g = newDeclaredGeneric(typ)
            val p = ParameterBinder(name, g)
            // cannot be lifted until has definition
            val r0 = if (isGlobal) {
              Value.GlobalReference(g.base, name)
            } else {
              Value.LocalReference(g.base)
            }
            val r: Leveled[Value.Reference] = Leveled.Fix(r0)
            (Layer.Defines(metas, defines :+ DefineItem(p, typ, r, null, isAxiom)) +: layers.tail, defines.size, g.base)
        }
      case _ => logicError()
    }
  }

  def newDefinitionChecked(index: Int, name: Name, code: dbi.Abstract) : (Self, Value.Reference) = {
    layers.head match {
      case Layer.Defines(metas, defines) =>
        defines(index) match {
          case DefineItem(typ0, typCode, r, c, ia) =>
            assert(typ0.name == name)
            assert(r.base.value == typ0.value.base)
            assert(null == c)
            assert(!ia)
            val nr = r match {
              case _: Leveled.Fix[Value.Reference] =>
                r.base.value = evalHack.eval(code)
                if (isGlobal) {
                  createGlobalFloating(r.base, code)
                } else {
                  r
                }
              case _ => logicError()
            }
            (Layer.Defines(metas, defines.updated(index, DefineItem(typ0, typCode, nr, code))) +: layers.tail, r.base)
        }
      case _ => logicError()
    }
  }




  def newParameterLayer(name: Name, typ: Value): (Self, Value) = {
    val g = Value.Generic(gen(), typ)
    val fix: Leveled[Value.Generic] = Leveled.Fix(g)
    (Layer.Parameter(ParameterBinder(name, fix), createMetas()) +: layers, g)
  }

  def newParameterLayerProvided(name: Name, g: Value.Generic): Self = {
    val fix = Leveled.Fix(g)
    Layer.Parameter(ParameterBinder(name, fix), createMetas()) +: layers
  }




  def newParametersLayer(hit: Option[Value] = None): Self =
    Layer.ParameterGraph(hit.map(a => HitDefinition(a, Seq.empty)), Seq.empty, Seq.empty, createMetas()) +: layers

  def newConstructor(name: Name, ims: Seq[Boolean], ps: semantic.ClosureGraph): Self =
    layers.head match {
      case Layer.ParameterGraph(alters,_, _, metas) =>
        alters match {
          case None => logicError()
          case Some(value) =>
            value.branches.find(_.name.intersect(name)) match {
              case Some(_) => logicError()
              case None =>
                assert(metas.debug_allFrozen)
                val n = AlternativeGraph(name, ims, ps)
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
            val v = Value.Generic(gen(), typ)
            if (!metas.debug_allFrozen) {
              logicError()
            }
            val fix: Leveled[Value.Generic] = Leveled.Fix(v)
            (Layer.ParameterGraph(alters, binders :+ ParameterBinder(name, fix), ds, metas) +: layers.tail, v)
        }
      case _ => logicError()
    }
  }

  def newDimension(name: Name): (Self, semantic.Formula.Generic) = {
    layers.head match {
      case Layer.ParameterGraph(alters, binders, ds, metas) =>
        binders.find(_.name.intersect(name)) match {
          case Some(_) => logicError()
          case _ =>
            val v = semantic.Formula.Generic(dgen())
            assert(metas.debug_allFrozen)

            (Layer.ParameterGraph(alters, binders, ds :+ DimensionBinder(name, v), metas) +: layers.tail, v)
        }
      case _ => logicError()
    }
  }



  def newPatternLayer(pattern: concrete.Pattern, typ: Value): (Self, Value, Pattern) = {
    val vvv = mutable.ArrayBuffer[Binder]()
    def recs(maps: Seq[(Boolean, concrete.Pattern)], imps: Seq[Boolean], nodes: semantic.ClosureGraph): (Seq[Value], Seq[Pattern], Seq[Name]) = {
      var ms = maps
      var vs =  Seq.empty[(Value, Pattern)]
      var graph = nodes
      for (i <- imps.indices) {
        if (maps.isEmpty) {
          if (!imps(i)) {
            throw PatternExtractException.WrongSize()
          }
        } else {
          if (imps(i) == ms.head._1) { // same implicit type
            val tv = rec(ms.head._2, graph(i).independent.typ, false)
            graph = graph.reduce(vs.size, tv._1)
            ms = ms.tail
            vs = vs :+ tv
          } else if (!imps(i)) {
            throw PatternExtractException.NotExpectingImplicit()
          } else {
            // it is a implicit which not introduced in concrete pattern
            val tv = rec(concrete.Pattern.Atom(Name.empty), graph(i).independent.typ, false)
            graph = graph.reduce(vs.size, tv._1)
            vs = vs :+ tv
          }
        }
      }
      if (ms.exists(_._1)) {
        throw PatternExtractException.ImplicitPatternForDimension()
      } else if (ms.size != nodes.dimSize) {
        throw PatternExtractException.WrongSize()
      } else if (!ms.forall(_._2.isInstanceOf[concrete.Pattern.Atom])) {
        throw PatternExtractException.NonAtomicPatternForDimension()
      }
      (vs.map(_._1), vs.map(_._2), ms.map(_._2.asInstanceOf[concrete.Pattern.Atom].id))
    }

    def rec(p: concrete.Pattern, t: Value, isRoot: Boolean): (Value, Pattern) = {
      p match {
        case concrete.Pattern.Atom(name) =>
          var ret: (Value, Pattern) = null
          var index = 0
          name.asRef match { // we make it as a reference here
            case Some(ref) =>
              t.whnf match {
                case sum: Value.Sum if { index = sum.etype.names.indexWhere(c => c.by(ref)); index >= 0 } =>
                  // TODO this handling is not that ok actually, if the sum has only implicit fields, but what's the use of this?
                  val c = sum.constructors(index)
                  if (c.isEmpty && c.dimSize == 0) {
                    ret = (Value.Construct(index, Seq.empty, Seq.empty, Map.empty), Pattern.Construct(index, Seq.empty))
                  } else {
                    throw PatternExtractException.WrongSize()
                  }
                case _ =>
              }
            case _ =>
          }
          if (ret == null) {
            val ggg = Value.Generic(gen(), t)
            val fix: Leveled.Fix[Value.Generic] = Leveled.Fix(ggg)
            val open = ParameterBinder(name, fix)
            vvv.append(open)
            ret = (ggg, Pattern.GenericValue)
          }
          ret
        case concrete.Pattern.Group(maps) =>
          t.whnf match {
            case r: Value.Record =>
              val (ms, ds, _) = recs(maps, r.etype.implicits, r.nodes)
              (Value.Make(ms), Pattern.Make(ds))
            case _ => throw PatternExtractException.MakeIsNotRecordType()
          }
        case concrete.Pattern.NamedGroup(name, maps) =>
          t.whnf match {
            case sum: Value.Sum =>
              if (!isRoot && sum.hit) throw PatternExtractException.HitPatternMatchingShouldBeAtRoot()
              val index = sum.etype.names.indexWhere(_.by(name))
              if (index >= 0) {
                val c = sum.constructors(index)
                val (ms, vs, names) = recs(maps, sum.etype.implicits(index), c)
                val ds = names.map(n => DimensionBinder(n, semantic.Formula.Generic(dgen())))
                vvv.appendAll(ds)
                val dds = ds.map(_.value)
                (Value.Construct(index, ms, dds, if (dds.isEmpty) Map.empty else c.reduceAll(ms).reduce(dds).restrictions()),
                  Pattern.Construct(index, vs ++ ds.map(_ => Pattern.GenericDimension)))
              } else {
                throw PatternExtractException.ConstructUnknownName()
              }
            case _ => throw PatternExtractException.ConstructNotSumType()
          }
      }
    }
    val (os, p) = rec(pattern, typ, true)
    val ctx: Self = Layer.PatternParameters(vvv.toSeq, createMetas()) +: layers
    (ctx, os, p)
  }
}
