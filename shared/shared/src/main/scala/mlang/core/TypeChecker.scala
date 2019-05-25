package mlang.core

import mlang.concrete.{Pattern => Patt, _}
import Context._
import mlang.concrete.Declaration.Modifier
import mlang.core
import mlang.name._
import mlang.utils._

import scala.collection.mutable
import scala.language.implicitConversions




sealed trait TypeCheckException extends CoreException

object TypeCheckException {


  // syntax
  case class FieldsDuplicated() extends TypeCheckException
  case class TagsDuplicated() extends TypeCheckException
  case class MustBeNamed() extends TypeCheckException
  case class EmptyTelescope() extends TypeCheckException
  case class EmptyArguments() extends TypeCheckException

  // elimination mismatch
  case class UnknownAsType() extends TypeCheckException
  case class UnknownProjection() extends TypeCheckException
  case class UnknownAsFunction() extends TypeCheckException


  case class CannotInferLambda() extends TypeCheckException
  case class CannotInferReturningTypeWithPatterns() extends TypeCheckException


  case class TypeMismatch() extends TypeCheckException

  case class ForbiddenModifier() extends TypeCheckException

  case class DeclarationWithoutDefinition() extends TypeCheckException

  case class ExpectingDimension() extends TypeCheckException

  case class PathEndPointsNotMatching() extends TypeCheckException
  case class InferPathEndPointsTypeNotMatching() extends TypeCheckException

  case class ExpectingLambdaTerm() extends TypeCheckException

  case class RemoveFalseFace() extends TypeCheckException
  case class CapNotMatching() extends TypeCheckException
  case class FacesNotMatching() extends TypeCheckException

  case class RequiresValidRestriction() extends TypeCheckException
  case class TermICanOnlyAppearInDomainOfFunction() extends TypeCheckException

  case class CannotInferMeta() extends TypeCheckException

  case class NotDefinedReferenceForTypeExpressions() extends TypeCheckException

  case class DimensionLambdaCannotBeImplicit() extends TypeCheckException

  case class NotExpectingImplicitArgument() extends TypeCheckException

  case class RecursiveTypesMustBeDefinedAtTopLevel() extends TypeCheckException

  case class UpCanOnlyBeUsedOnTopLevelDefinition()  extends TypeCheckException
}


object TypeChecker {
  private val pgen = new LongGen.Positive()
  private val igen = new LongGen.Positive()
  def topLevel(): TypeChecker = new TypeChecker(Seq.empty).newDefinesLayer()
}

class TypeChecker private (protected override val layers: Layers)
    extends ContextBuilder with BaseEvaluator with PlatformEvaluator with Unify {

  override type Self = TypeChecker

  override protected implicit def create(a: Layers): Self = new TypeChecker(a)


  def checkValidRestrictions(ds0: Seq[Value.DimensionPair]) = {
  }

  def checkCompatibleCapAndFaces(
      ident: Name,
      faces: Seq[Term.Face],
      bt: Value.AbsClosure,
      bv: Value,
      dv: Value.DimensionPair
  ): Seq[Abstract.Face] = {
    // we use this context to evaluate body of faces, it is only used to keep the dimension binding to the same
    // one, but as restricts is already present in abstract terms, it is ok to use this instead of others
    val (_, dim0) = newParametersLayer().newDimensionLayer(ident)
    val btt = bt(dim0)
    val res = faces.map(a => {
      val (dav, daa) = checkDimensionPair(a.dimension)
      if (dav.isFalse) {
        throw TypeCheckException.RemoveFalseFace()
      } else {
        val ctx0 = newRestrictionLayer(dav)
        val (ctx, fd) = ctx0.newDimensionLayer(ident, Some(dim0))
        val btr = bt(fd).restrict(dav)
        val na = Abstract.AbsClosure(ctx.finishReify(), ctx.check(a.term, btr))
        val naa = ctx0.eval(na)
        val nv = naa(dv.from)
        if (!unifyTerm(btr, bv.restrict(dav), nv)) {
          throw TypeCheckException.CapNotMatching()
        }
        (Abstract.Face(daa, na), naa(dim0), dav)
      }
    })
    for (i <- faces.indices) {
      val l = res(i)
      for (j <- 0 until i) {
        val r = res(j)
        // this might evaluate the dimensions to new values
        val dfv = r._3.restrict(l._3)
        // only used to test if this restriction is false face or not
        if (!dfv.isFalse) {
          if (!unifyTerm(
            btt.restrict(l._3).restrict(dfv),
            l._2.restrict(dfv),
            r._2.restrict(l._3))) {
            throw TypeCheckException.FacesNotMatching()
          }
        }
      }
    }
    if (!Value.DimensionPair.checkValidRestrictions(res.map(_._3))) {
      throw TypeCheckException.RequiresValidRestriction()
    }
    res.map(_._1)
  }


  def checkLine(a: Term): (Value.AbsClosure, Abstract.AbsClosure) = {
    a match {
      case Term.Lambda(n, b, body) =>
        if (b) throw TypeCheckException.DimensionLambdaCannotBeImplicit()
        val ctx = newDimensionLayer(n)._1
        val (_, ta0) = ctx.inferLevel(body)
        val ta = Abstract.AbsClosure(ctx.finishReify(), ta0)
        val tv = eval(ta)
        (tv, ta)
      case _ => throw TypeCheckException.ExpectingLambdaTerm()
    }
  }

  private def finishOffImplicits(v: Value, abs: Abstract): (Value, Abstract) = {
    v.whnf match {
      case Value.Function(d, i, c) if i =>
        val (mv, ma) = newMeta(d)
        finishOffImplicits(c(mv), Abstract.App(abs, ma))
      case _ => (v, abs)
    }
  }

  private def infer(term: Term, noReduceMore: Boolean = false): (Value, Abstract) = {
    debug(s"infer $term")
    def reduceMore(v: Value, abs: Abstract): (Value, Abstract) = {
      if (noReduceMore) {
        (v, abs)
      } else {
        finishOffImplicits(v, abs)
      }
    }
    val res = term match {
      case Term.Universe(i) =>
        (Value.Universe.suc(i), Abstract.Universe(i))
      case Term.Up(a, b) =>
        val (binder, abs) = lookupTerm(a.name)
        abs match {
          case Abstract.Reference(up, _) if up == layers.size - 1 =>
            reduceMore(binder.up(b), Abstract.Up(abs, b))
          case _ => throw TypeCheckException.UpCanOnlyBeUsedOnTopLevelDefinition()
        }
      case Term.Reference(name) =>
        // should lookup always return a value? like a open reference?
        val (binder, abs) = lookupTerm(name)
        reduceMore(binder, abs)
      case Term.Hole =>
        throw TypeCheckException.CannotInferMeta()
      case Term.ConstantDimension(_) =>
        throw ContextException.ConstantSortWrong()
      case Term.I =>
        throw TypeCheckException.TermICanOnlyAppearInDomainOfFunction()
      case Term.Cast(v, t) =>
        val (_, ta) = inferLevel(t)
        val tv = eval(ta)
        (tv, check(v, tv))
      case Term.Function(domain, codomain) =>
        if (domain.isEmpty) throw TypeCheckException.EmptyTelescope()
        val (l, v) = inferTelescope(NameType.flatten(domain), codomain)
        (Value.Universe(l), v)
      case r@Term.Record(fields) =>
        for (f <- fields) {
          if (f.names.isEmpty) throw TypeCheckException.MustBeNamed()
        }
        for (i <- r.names.indices) {
          for (j <- (i + 1) until r.names.size) {
            if (r.names(i)._2 intersect r.names(j)._2) {
              throw TypeCheckException.FieldsDuplicated()
            }
          }
        }
        val (fl, fs) = newLayerInferFlatLevel(fields)
        (Value.Universe(fl), Abstract.Record(fl, None, fs.map(_._1), fs.map(_._2), fs.map(a => (a._3.term.termDependencies(0).toSeq.sorted, a._3))))
      case Term.Sum(constructors) =>
        for (i <- constructors.indices) {
          for (j <- (i + 1) until constructors.size) {
            if (constructors(i).name.intersect(constructors(j).name)) {
              throw TypeCheckException.TagsDuplicated()
            }
          }
        }
        // TODO in case of HIT, each time a constructor finished, we need to construct a partial sum and update the value
        val fs = constructors.map(c => newLayerInferFlatLevel(c.term))
        val fl = fs.map(_._1).max
        (Value.Universe(fl), Abstract.Sum(fl, None, fs.map(_._2).zip(constructors).map(a =>
          Abstract.Constructor(a._2.name, a._1.map(k => k._2), a._1.zipWithIndex.map(kk => (0 until kk._2, kk._1._3))))))
      case Term.Coe(direction, tp, base) =>
        // LATER does these needs finish off implicits?
        val (dv, da) = checkDimensionPair(direction)
        val (cl, ta) = checkLine(tp)
        val la = check(base, cl(dv.from))
        (cl(dv.to), Abstract.Coe(da, ta, la))
      case Term.Com(direction, tp, base, ident, faces) =>
        val (dv, da) = checkDimensionPair(direction)
        val (cl, ta) = checkLine(tp)
        val ba = check(base, cl(dv.from))
        val rs = checkCompatibleCapAndFaces(ident, faces, cl, eval(ba), dv)
        (cl(dv.to), Abstract.Com(da, ta, ba, rs))
      case Term.Hcom(direction, base, ident, faces) =>
        val (dv, da)= checkDimensionPair(direction)
        val (bt, ba) = infer(base)
        val bv = eval(ba)
        val rs = checkCompatibleCapAndFaces(ident, faces, Value.AbsClosure(bt), bv, dv)
        (bt, Abstract.Hcom(da, reify(bt), ba, rs))
      case Term.PathType(typ, left, right) =>
        typ match {
          case Some(tp) =>
            tp match {
              case Term.Lambda(name, b, body) =>
                if (b) throw TypeCheckException.DimensionLambdaCannotBeImplicit()
                val ctx = newDimensionLayer(name)._1
                val (tl, ta) = ctx.inferLevel(body)
                val ca = Abstract.AbsClosure(ctx.finishReify(), ta)
                val tv = eval(ca)
                val la = check(left, tv(Value.Dimension.False))
                val ra = check(right, tv(Value.Dimension.True))
                (Value.Universe(tl), Abstract.PathType(ca, la, ra))
              case _ => throw TypeCheckException.ExpectingLambdaTerm()
            }
          case None =>
            val (lt, la) = infer(left)
            val (rt, ra) = infer(right)
            val ttt = if (subTypeOf(lt, rt)) {
              Some(rt)
            } else if (subTypeOf(rt, lt)) {
              Some(lt)
            } else None
            ttt match {
              case Some(t) =>
                val ta = newDimensionLayer(Name.empty)._1.reify(t)
                if (debug.enabled) debug(s"infer path type: $ta")
                (Value.Universe(Value.inferLevel(t)), Abstract.PathType(Abstract.AbsClosure(Seq.empty, ta), la, ra))
              case None =>
                throw TypeCheckException.InferPathEndPointsTypeNotMatching()
            }
        }
      case p: Term.PatternLambda =>
        throw TypeCheckException.CannotInferReturningTypeWithPatterns()
      case l: Term.Lambda =>
        throw TypeCheckException.CannotInferLambda()
      case Term.Projection(left, right) =>
        val (lt, la) = infer(left)
        val lv = eval(la)
        lazy val ltr = lt.whnf.asInstanceOf[Value.Record]
        def error() = throw TypeCheckException.UnknownProjection()
        var index = -1
        lv.whnf match {
          case m: Value.Make if { index = ltr.names.indexWhere(_.by(right)) ; index >= 0 } =>
            reduceMore(ltr.projectedType(m.values, index), Abstract.Projection(la, index))
          // TODO user defined projections for a type, i.e.
          // TODO [issue 7] implement const_projections syntax
          case r: Value.Record if right == Ref.make =>
            reduceMore(r.makerType, Abstract.Maker(la, -1))
          case r: Value.Sum if { index = r.constructors.indexWhere(_.name.by(right)); index >= 0 } =>
            reduceMore(r.constructors(index).makerType, Abstract.Maker(la, index))
          case _ => error()
        }
      case Term.App(lambda, arguments) =>
        if (arguments.isEmpty) throw TypeCheckException.EmptyArguments()
        val (lt, la) = infer(lambda, true)
        val (v1, v2) = inferApp(lt, la, arguments)
        reduceMore(v1, v2) // because inferApp stops when arguments is finished
      case Term.Let(declarations, in) =>
        val (ctx, ms, da) = newDefinesLayer().checkDeclarations(declarations, false)
        val (it, ia) = ctx.infer(in)
        val ms0 = ctx.freezeReify()
        (it, Abstract.Let(ms ++ ms0, da, ia))

    }
    debug(s"infer result ${res._2}")
    res
  }

  private def checkDimensionPair(p: Term.Pair): (Value.DimensionPair, Abstract.DimensionPair) = {
    val (a, b) = checkDimension(p.from)
    val (c, d) = checkDimension(p.to)
    (Value.DimensionPair(a, c), Abstract.DimensionPair(b, d))
  }

  private def checkDimension(r: Term): (Value.Dimension, Abstract.Dimension) = {
    r match {
      case Term.Reference(name) =>
        val (v, a) = lookupDimension(name)
        (v, a)
      case Term.ConstantDimension(i) =>
        if (i) {
          (Value.Dimension.True, Abstract.Dimension.True)
        } else {
          (Value.Dimension.False, Abstract.Dimension.False)
        }
      case _ => throw TypeCheckException.ExpectingDimension()
    }
  }

  private def newLayerInferFlatLevel(terms: Seq[NameType]): (Int, Seq[(Name, Boolean, Abstract.MetaEnclosed)]) = {
    var ctx = newParametersLayer()
    var l = 0
    val fas = terms.flatMap(f => {
      val fs = NameType.flatten(Seq(f))
      fs.map(n => {
        val (fl, fa) = ctx.inferLevel(f.ty)
        l = l max fl
        val ms = ctx.freezeReify()
        ctx = ctx.newParameter(n._2, ctx.eval(fa))._1
        (n._2, n._1, Abstract.MetaEnclosed(ms, fa))
      })
    })
    (l, fas)
  }

  private def inferTelescope(domain: NameType.FlatSeq, codomain: Term): (Int, Abstract) = {
    domain match {
      case head +: tail =>
        head._3 match {
          case Term.I =>
            if (head._1) throw TypeCheckException.DimensionLambdaCannotBeImplicit()
            val ctx = newDimensionLayer(head._2)._1
            val (cl, ca) = ctx.inferTelescope(tail, codomain)
            (cl, Abstract.PathType(Abstract.AbsClosure(ctx.finishReify(), ca), ???, ???))
          case _ =>
            val (dl, da) = inferLevel(head._3)
            val ctx = newParameterLayer(head._2, eval(da))._1
            val (cl, ca) = ctx.inferTelescope(tail, codomain)
            (dl max cl, Abstract.Function(da, head._1, Abstract.Closure(ctx.finishReify(), ca)))
        }
      case Seq() =>
        val (l, a) = inferLevel(codomain)
        (l, a)
    }
  }

  private def inferApp(lt: Value, la: Abstract, arguments: Seq[(Boolean, Term)]): (Value, Abstract) = {
    arguments match {
      case head +: tail =>
        lt.whnf match {
          case f@Value.Function(domain, fimp, codomain) =>
            if (fimp == head._1) {
              val aa = check(head._2, domain)
              val av = eval(aa)
              val lt1 = codomain(av)
              val la1 = Abstract.App(la, aa)
              inferApp(lt1, la1, tail)
            } else if (fimp) {
              val (lt1, la1) = finishOffImplicits(f, la)
              inferApp(lt1, la1, arguments)
            } else {
              throw TypeCheckException.NotExpectingImplicitArgument()
            }
          case Value.PathType(typ, _, _) =>
            if (head._1) throw TypeCheckException.DimensionLambdaCannotBeImplicit()
            val (dv, da) = checkDimension(head._2)
            val lt1 = typ(dv)
            val la1 = Abstract.PathApp(la, da)
            inferApp(lt1, la1, tail)
          // TODO user defined applications
          case _ => throw TypeCheckException.UnknownAsFunction()
        }
      case Seq() =>
        (lt, la)
    }
  }

  private def check(
      term: Term,
      cp: Value,
      lambdaNameHints: Seq[Name] = Seq.empty
  ): Abstract = {
    debug(s"check $term")
    val (hint, tail) = lambdaNameHints match {
      case head +: tl => (head, tl)
      case _ => (Name.empty, Seq.empty)
    }
    def fallback(): Abstract = {
      term match {
        case Term.Hole =>
          newMeta(cp)._2
        case _ =>
          val (tt, ta) = infer(term)
          if (subTypeOf(tt, cp)) ta
          else {
            info(s"${reify(tt.whnf)}")
            info(s"${reify(cp.whnf)}")
            throw TypeCheckException.TypeMismatch()
          }
      }
    }
    cp.whnf match {
      case Value.Function(domain, fimp, codomain) =>
        term match {
          case Term.Lambda(n, limp, body) if fimp == limp =>
            val (ctx, v) = newParameterLayer(n.nonEmptyOrElse(hint), domain)
            val ba = ctx.check(body, codomain(v), tail)
            Abstract.Lambda(Abstract.Closure(ctx.finishReify(), ba))
          case Term.PatternLambda(limp, cases) if fimp == limp =>
            Abstract.PatternLambda(TypeChecker.pgen(), reify(codomain), cases.map(c => {
              val (ctx, v, pat) = newPatternLayer(c.pattern, domain)
              val ba = ctx.check(c.body, codomain(v), tail)
              Abstract.Case(pat, Abstract.MultiClosure(ctx.finishReify(), ba))
            }))
          case _ =>
            if (fimp) {
              val (ctx, v) = newParameterLayer(Name.empty, domain)
              val ba = ctx.check(term, codomain(v), tail)
              Abstract.Lambda(Abstract.Closure(ctx.finishReify(), ba))
            } else {
              fallback()
            }
        }
      case Value.PathType(typ, left, right) =>
        term match {
          case Term.Lambda(n, b, body) =>
            if (b) throw TypeCheckException.DimensionLambdaCannotBeImplicit()
            val (c1, dv) = newDimensionLayer(n.nonEmptyOrElse(hint))
            val t1 = typ(dv)
            import Value.Dimension._
            val a1 = c1.check(body, t1, tail)
            val ps = Abstract.AbsClosure(c1.finishReify(), a1)
            val pv = eval(ps)
            val leftEq = unifyTerm(typ(False), pv(False), left)
            val rightEq = unifyTerm(typ(True), pv(True), right)
            if (leftEq && rightEq) {
              Abstract.PathLambda(ps)
            } else {
              throw TypeCheckException.PathEndPointsNotMatching()
            }
          case _ => fallback()
        }
      case _ => fallback()
    }
  }


  private def checkDeclaration(
      s: Declaration,
      mis: mutable.ArrayBuffer[CodeInfo[Value.Meta]],
      vis: mutable.ArrayBuffer[DefinitionInfo], topLevel: Boolean): Self = {
    def wrapBody(t: Term, imp: Seq[Boolean]): Term = if (imp.isEmpty) t else wrapBody(Term.Lambda(Name.empty, imp.last, t), imp.dropRight(1))
    def appendMetas(ms: Seq[Value.Meta]): Unit = {
      for (m <- ms) {
        mis.append(CodeInfo(reify(m.solved), m))
      }
    }
    def reevalStuff(ctx: TypeChecker, changed: Dependency): Unit = {
      val done = mutable.ArrayBuffer.empty[Dependency]
      // the reason it needs to rec, is that we have whnf remembered
      def rec(c: Dependency): Unit = {
        done.append(c)
        for (i <- mis.indices) {
          val m = mis(i)
          val handle = Dependency(i, true)
          if (!done.contains(handle) && m.dependencies.contains(changed)) {
            m.t.v = Value.Meta.Closed(ctx.eval(m.code))
            rec(handle)
          }
        }
        for (i <- vis.indices) {
          val v = vis(i)
          val handle = Dependency(i, false)
          if (!done.contains(handle)) {
            var needs = false
            if (v.typ.dependencies.contains(changed)) needs = true
            v.code match {
              case Some(value) => // if references to self, already handled
                if (value.dependencies.contains(changed)) needs = true
              case _ =>
            }
            if (needs) {
              info(s"re-eval dependency ${ctx.layers.head.asInstanceOf[Layer.Defines].terms(i).name}")
              v.typ.t.typ = ctx.eval(v.typ.code)
              v.code match {
                case Some(value) => // if references to self, already handled
                  value.t.value = ctx.eval(value.code)
                case _ =>
              }
              rec(handle)
            }
          }
        }
      }
      rec(changed)
    }
    if (s.modifiers.contains(Declaration.Modifier.__Debug)) {
      val a = 1
    }
    s match {
      case Declaration.Define(ms, name, ps, t0, v) =>
        // TODO implement with constructor
//        if (ms.contains(Modifier.WithConstructor)) {
//        }
        // a inductive type definition
        var inductively =
          if (ms.contains(Modifier.Inductively)) {
            if (topLevel) {
              Abstract.Inductively(TypeChecker.igen())
            } else {
              throw TypeCheckException.RecursiveTypesMustBeDefinedAtTopLevel()
            }
          } else null
        val ret = t0 match {
          case Some(t) =>
            // term with type
            info(s"define $name")
            val pps = NameType.flatten(ps)
            val (_, ta) = inferTelescope(pps, t)
            appendMetas(freeze())
            val tv = eval(ta)
            val (ctx, index, generic) = newDeclaration(name, tv) // allows recursive definitions
            fillTo(vis, index); assert(vis(index) == null)
            vis.update(index, DefinitionInfo(None, CodeInfo(ta, generic)))
            val lambdaNameHints = pps.map(_._2) ++(t match {
              case Term.Function(d, _) =>
                NameType.flatten(d).map(_._2)
              case _ => Seq.empty
            })
            val va0 = ctx.check(wrapBody(v, pps.map(_._1)), tv, lambdaNameHints)
            val va = if (inductively != null) {
              if (pps.nonEmpty) {
                warn("we don't support parameterized inductive type yet")
                ???
              }
              val tt = Some(inductively)
              va0 match {
                case s: Abstract.Sum => inductively = null; assert(s.inductively.isEmpty); s.copy(inductively = tt)
                case s: Abstract.Record => inductively = null; assert(s.inductively.isEmpty); s.copy(inductively = tt)
                case ig => ig
              }
            } else {
              va0
            }
            appendMetas(ctx.freeze())
            val ref = Value.Reference(null) // the reason we
            val ctx2 = ctx.newDefinitionChecked(index, name, ref)
            ref.value = ctx2.eval(va) // we want to eval it under the context with reference to itself
            vis(index).code = Some(CodeInfo(va, ref))
            // you don't need to reevaluate stuff here, no one reference me now!
            info(s"defined $name")
            ctx2
          case None =>
            // term without type
            if (ps.nonEmpty) ???
            lookupDefined(name) match {
              case None => // needs to infer a type
                info(s"infer $name")
                val (vt, va) = infer(v)
                appendMetas(freeze())
                val ta = reify(vt)
                val ref = Value.Reference(eval(va))
                val (ctx, index, generic) = newDefinition(name, vt, ref)
                fillTo(vis, index); assert(vis(index) == null)
                vis.update(index, DefinitionInfo(Some(CodeInfo(va, ref)), CodeInfo(ta, generic)))
                info(s"inferred $name")
                ctx
              case Some((index, typ)) => // needs to check against defined type
                info(s"check defined $name")
                val va = check(v, typ, Seq.empty)
                appendMetas(freeze())
                val ref = Value.Reference(null)
                val ctx = newDefinitionChecked(index, name, ref)
                ref.value = ctx.eval(va)
                vis(index).code = Some(CodeInfo(va, ref))
                reevalStuff(ctx, Dependency(index, false))
                info(s"checked $name")
                ctx
            }
        }
        if (inductively != null) warn(s"${name.toString} is not a inductive type but has modifier inductively")
        ret
      case Declaration.Declare(ms, name, ps, t) =>
        info(s"declare $name")
        if (ms.exists(_ != Modifier.__Debug)) throw TypeCheckException.ForbiddenModifier()
        val (_, ta) = inferTelescope(NameType.flatten(ps), t)
        appendMetas(freeze())
        val tv = eval(ta)
        val (ctx, index, generic) = newDeclaration(name, tv)
        fillTo(vis, index); assert(vis(index) == null)
        vis.update(index, DefinitionInfo(None, CodeInfo(ta, generic)))
        info(s"declared $name")
        ctx
    }
  }

  private def checkDeclarations(seq: Seq[Declaration], topLevel: Boolean): (Self, Seq[Abstract], Seq[Abstract]) = {
    // how to handle mutual recursive definitions, calculate strong components
    var ctx = this
    val ms0 = mutable.ArrayBuffer.empty[CodeInfo[Value.Meta]]
    val vs0 = mutable.ArrayBuffer.empty[DefinitionInfo]
    for (s <- seq) {
      val ctx0 = ctx.checkDeclaration(s, ms0, vs0, topLevel)
      ctx = ctx0
    }
    // this is a hack because we don't have modules yet
    val ms = ms0.dropWhile(_ == null)
    val vs = vs0.dropWhile(_ == null)
    if (vs.exists(a => a.code.isEmpty)) {
      throw TypeCheckException.DeclarationWithoutDefinition()
    }
    (ctx, ms.map(_.code), vs.map(_.code.get.code))
  }



  private def inferLevel(term: Term): (Int, Abstract) = {
    val (tt, ta) = infer(term)
    tt.whnf match {
      case Value.Universe(l) => (l, ta)
      // TODO user defined type coercion
      case _ => throw TypeCheckException.UnknownAsType()
    }
  }


  def check(m: Module): TypeChecker = Benchmark.TypeChecking {
    checkDeclarations(m.declarations, true)._1
  }
}

private case class CodeInfo[T](
    code: Abstract,
    t: T) {
  val dependencies = code.dependencies(0)
}
private case class DefinitionInfo(
    var code: Option[CodeInfo[Value.Reference]],
    typ: CodeInfo[Value.Generic])

