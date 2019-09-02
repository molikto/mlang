package mlang.compiler

import mlang.compiler.Concrete._
import ElaborationContext._
import Declaration.Modifier
import mlang.utils._

import scala.collection.mutable
import scala.language.implicitConversions



object Elaborator {
  private val pgen = new LongGen.Positive()
  private val igen = new LongGen.Positive()
  def topLevel(): Elaborator = new Elaborator(Seq.empty).newDefinesLayer()
}

class Elaborator private(protected override val layers: Layers)
    extends ElaborationContextBuilder with Evaluator with PlatformEvaluator with Unify {

  override type Self = Elaborator

  override protected implicit def create(a: Layers): Self = new Elaborator(a)

  def checkValidRestrictions(ds0: Seq[Value.Dimension]) = {
    ???
  }

  def checkCompatibleCapAndFaces(
                                  faces: Seq[Concrete.Face],
                                  bt: Value.AbsClosure,
                                  bv: Value,
                                  dv: Value.Dimension
  ): Seq[Abstract.Face] = {
    /*
    // we use this context to evaluate body of faces, it is only used to keep the dimension binding to the same
    // one, but as restricts is already present in abstract terms, it is ok to use this instead of others
    val (_, dim0) = newParametersLayer().newDimensionLayer(Name.empty)
    val btt = bt(dim0)
    val res = faces.map(a => {
      val (dav, daa) = checkDimension(a.dimension)
      if (dav.isFalse) {
        throw ElaboateException.RemoveFalseFace()
      } else {
        val ctx0 = newRestrictionLayer(dav)
        val btr = bt.restrict(dav)
        // FIXME no hurry to finalize this context? use information in cap to infer?
        // currently if we want a refl face, it cannot do this!!
        val na = ctx0.checkLine(a.term, dim0, btr)
        val naa = ctx0.eval(na)
        val nv = naa(dv.from)
        if (!unifyTerm(btr(dim0), bv.restrict(dav), nv)) {
          throw ElaboateException.CapNotMatching()
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
            r._2.restrict(l._3.restrict(r._3)))) {
            throw ElaboateException.FacesNotMatching()
          }
        }
      }
    }
    if (!Value.DimensionPair.checkValidRestrictions(res.map(_._3))) {
      throw ElaboateException.RequiresValidRestriction()
    }
    res.map(_._1)
    */
    ???
  }


  def checkLine(a: Concrete, dim: Value.Dimension.Generic, typ: Value.AbsClosure): Abstract.AbsClosure = {
    a match {
      case Concrete.Lambda(n, b, body) =>
        if (b) throw ElaborateException.DimensionLambdaCannotBeImplicit()
        val ctx = newDimensionLayer(n, dim)
        val ta = ctx.check(body, typ(dim))
        Abstract.AbsClosure(ctx.finishReify(), ta)
      case _ =>
        val ctx = newDimensionLayer(Name.empty)._1 // it is ok to infer in this context, as the name is empty so it doesn't affect much
        val (tv, ta) = ctx.infer(a)
        tv.whnf match {
          case j@Value.PathType(_, _, _) =>
            Abstract.AbsClosure(ctx.finishReify(), Abstract.PathApp(ta, Abstract.Dimension.Reference(0)))
          case _ => throw ElaborateException.ExpectingLambdaTerm()
        }
    }
  }
  def checkTypeLine(a: Concrete): (Int, Abstract.AbsClosure) = {
    a match {
      case Concrete.Lambda(n, b, body) =>
        if (b) throw ElaborateException.DimensionLambdaCannotBeImplicit()
        val ctx = newDimensionLayer(n)._1
        val (l, ta0) = ctx.inferLevel(body)
        val ta = Abstract.AbsClosure(ctx.finishReify(), ta0)
        (l, ta)
      case _ =>
        val ctx = newDimensionLayer(Name.empty)._1
        val (tv, ta) = ctx.infer(a)
        tv.whnf match {
          case j@Value.PathType(_, _, _) =>
            val clo = Abstract.AbsClosure(ctx.finishReify(), Abstract.PathApp(ta, Abstract.Dimension.Reference(0)))
            (Value.inferLevel(j), clo)
          case _ => throw ElaborateException.ExpectingLambdaTerm()
        }
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

  private def infer(term: Concrete, noReduceMore: Boolean = false): (Value, Abstract) = {
    debug(s"infer $term")
    def reduceMore(v: Value, abs: Abstract): (Value, Abstract) = {
      if (noReduceMore) {
        (v, abs)
      } else {
        finishOffImplicits(v, abs)
      }
    }
    val res = term match {
      case Concrete.Type =>
        (Value.Universe.level1, Abstract.Universe(0))
      case Concrete.Up(a, b) =>
        a match {
          case Concrete.Up(c, d) =>
            infer(Concrete.Up(c, b + d))
          case Concrete.Type =>
            (Value.Universe(b + 1), Abstract.Universe(b))
          case Concrete.Reference(ref) =>
            val (binder, abs) = lookupTerm(ref)
            abs match {
              case Abstract.Reference(up, _) if up == layers.size - 1 =>
                reduceMore(binder.up(b), Abstract.Up(abs, b))
              case _ => throw ElaborateException.UpCanOnlyBeUsedOnTopLevelDefinitionOrUniverse()
            }
          case _ => throw ElaborateException.UpCanOnlyBeUsedOnTopLevelDefinitionOrUniverse()
        }
      case Concrete.Reference(name) =>
        // should lookup always return a value? like a open reference?
        val (binder, abs) = lookupTerm(name)
        reduceMore(binder, abs)
      case Concrete.Hole =>
        throw ElaborateException.CannotInferMeta()
      case Concrete.True =>
        throw ElaborationContextException.ConstantSortWrong()
      case Concrete.False =>
        throw ElaborationContextException.ConstantSortWrong()
      case Concrete.I =>
        throw ElaborateException.TermICanOnlyAppearInDomainOfFunction()
      case Concrete.Make =>
        throw ElaborateException.CannotInferMakeExpression()
      case _: Concrete.VMake =>
        throw ElaborateException.CannotInferVMakeExpression()
      case Concrete.Cast(v, t) =>
        val (_, ta) = inferLevel(t)
        val tv = eval(ta)
        (tv, check(v, tv))
      case Concrete.Function(domain, codomain) =>
        if (domain.isEmpty) throw ElaborateException.EmptyTelescope()
        val (l, v) = inferTelescope(NameType.flatten(domain), codomain)
        (Value.Universe(l), v)
      case r@Concrete.Record(fields) =>
        for (f <- fields) {
          if (f.names.isEmpty) throw ElaborateException.MustBeNamed()
        }
        for (i <- r.names.indices) {
          for (j <- (i + 1) until r.names.size) {
            if (r.names(i)._2 intersect r.names(j)._2) {
              throw ElaborateException.FieldsDuplicated()
            }
          }
        }
        val (fl, fs) = newLayerInferFlatLevel(fields)
        (Value.Universe(fl), Abstract.Record(None, fs.map(_._1), fs.map(_._2), fs.map(a => (a._3.term.termDependencies(0).toSeq.sorted, a._3))))
      case Concrete.Sum(constructors) =>
        for (i <- constructors.indices) {
          for (j <- (i + 1) until constructors.size) {
            if (constructors(i).name.intersect(constructors(j).name)) {
              throw ElaborateException.TagsDuplicated()
            }
          }
        }
        // TODO in case of HIT, each time a constructor finished, we need to construct a partial sum and update the value
        val fs = constructors.map(c => newLayerInferFlatLevel(c.term))
        val fl = fs.map(_._1).max
        (Value.Universe(fl), Abstract.Sum(None, fs.map(_._2).zip(constructors).map(a =>
          Abstract.Constructor(a._2.name, a._1.map(k => k._2), a._1.zipWithIndex.map(kk => (0 until kk._2, kk._1._3))))))
      case Concrete.Coe(direction, tp, base) =>
        // LATER does these needs finish off implicits?
        ???
        /*
        val (dv, da) = checkDimension(direction)
        val (_, ta) = checkTypeLine(tp)
        val cl = eval(ta)
        val la = check(base, cl(Dimension.False))
        (cl(Dimension.True), Abstract.Coe(da, ta, la))
        */
      case Concrete.Com(direction, tp, base, faces) =>
        ???
        /*
        val (dv, da) = checkDimension(direction)
        val (_, ta) = checkTypeLine(tp)
        val cl = eval(ta)
        val ba = check(base, cl(Dimension.False))
        val rs = checkCompatibleCapAndFaces(faces, cl, eval(ba), dv)
        (cl(dv.to), Abstract.Com(da, ta, ba, rs))
         */
      case Concrete.Hcom(direction, base, faces) =>
        ???
        /*
        val (dv, da)= checkDimension(direction)
        val (bt, ba) = infer(base)
        val bv = eval(ba)
        val rs = checkCompatibleCapAndFaces(faces, Value.AbsClosure(bt), bv, dv)
        val btr = reify(bt)
        debug(s"infer hcom type $btr", 1)
        (bt, Abstract.Hcom(da, btr, ba, rs))
        */
      case Concrete.PathType(typ, left, right) =>
        typ match {
          case Some(tp) =>
            val (tl, ca) = checkTypeLine(tp)
            val tv = eval(ca)
            val la = check(left, tv(Value.Dimension.False))
            val ra = check(right, tv(Value.Dimension.True))
            (Value.Universe(tl), Abstract.PathType(ca, la, ra))
          case None =>
            // FIXME instead of inferring two side, infer one side then check another; or if we have meta with levels... can we just write a max level? it seems not that easy... because you run into the same kind of problems
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
                debug(s"infer path type $ta", 1)
                (Value.Universe(Value.inferLevel(t)), Abstract.PathType(Abstract.AbsClosure(Seq.empty, ta), la, ra))
              case None =>
                throw ElaborateException.InferPathEndPointsTypeNotMatching()
            }
        }
      case Concrete.VProj(m) =>
        val (mt, ma) = infer(m)
         mt match {
          case Value.VType(x, _, b, e) =>
            (b, Abstract.VProj(rebindDimension(x), ma, Abstract.Projection(reify(e), 0)))
          case _ => throw ElaborateException.VProjCannotInfer()
        }
      case p: Concrete.PatternLambda =>
        throw ElaborateException.CannotInferReturningTypeWithPatterns()
      case l: Concrete.Lambda =>
        throw ElaborateException.CannotInferLambda()
      case Concrete.Projection(left, right) =>
        val (lt, la) = infer(left)
        val lv = eval(la)
        lazy val ltr = lt.whnf.asInstanceOf[Value.Record]
        def error() = throw ElaborateException.UnknownProjection()
        var index = -1
        def calIndex(a: Text => Int) = {
          index = right match {
            case Concrete.Reference(name) => a(name)
            case _ => -1
          }
          index >= 0
        }
        lt.whnf match {
          case m: Value.Record if calIndex(t => ltr.names.indexWhere(_.by(t))) =>
            reduceMore(m.projectedType(lv, index), Abstract.Projection(la, index))
          case _ =>
            lv.whnf match {
              // TODO user defined projections for a type, i.e.
              // TODO [issue 7] implement const_projections syntax
              case r: Value.Record if right == Concrete.Make =>
                reduceMore(r.makerType, Abstract.Maker(la, -1))
              case r: Value.Sum if calIndex(t => r.constructors.indexWhere(_.name.by(t))) =>
                reduceMore(r.constructors(index).makerType, Abstract.Maker(la, index))
              case _ => error()
            }
        }
      case Concrete.App(lambda, arguments) =>
        if (arguments.isEmpty) throw ElaborateException.EmptyArguments()
        val (lt, la) = infer(lambda, true)
        val (v1, v2) = inferApp(lt, la, arguments)
        reduceMore(v1, v2) // because inferApp stops when arguments is finished
      case Concrete.VType(x, a, b, e) =>
        ???
//        val (xv, xa) = checkDimension(x)
//        xv match {
//          case g: Dimension.Generic =>
//            val dp = Value.DimensionPair(g, Value.Dimension.False)
//            val ctxr1 = newRestrictionLayer(dp)
//            val (al, aa0) = ctxr1.inferLevel(a)
//            val aa = Abstract.MetaEnclosed(ctxr1.finishReify(), aa0)
//            val (bl, ba) = inferLevel(b)
//            val ctxr2 = newRestrictionLayer(dp)
//            val ea = ctxr2.check(e, Value.App(Value.App(Value.equiv, ctxr1.eval(aa0)), eval(ba).restrict(dp)))
//            (Value.Universe(al max bl), Abstract.VType(xa, aa, ba, Abstract.MetaEnclosed(ctxr2.finishReify(), ea)))
//          case _ =>
//            throw TypeCheckException.RemoveConstantVType()
//        }
      case Concrete.Let(declarations, in) =>
        val (ctx, ms, da) = newDefinesLayer().checkDeclarations(declarations, false)
        val (it, ia) = ctx.infer(in)
        val ms0 = ctx.freezeReify()
        (it, Abstract.Let(ms ++ ms0, da, ia))
    }
    debug(s"infer result ${res._2}")
    res
  }

  private def checkDimension(r: Concrete): (Value.Dimension, Abstract.Dimension) = {
    r match {
      case Concrete.Reference(name) =>
        val (v, a) = lookupDimension(name)
        (v, a)
      case Concrete.True =>
        (Value.Dimension.True, Abstract.Dimension.True)
      case Concrete.False =>
        (Value.Dimension.False, Abstract.Dimension.False)
      case _ => throw ElaborateException.ExpectingDimension()
    }
  }

  private def newLayerInferFlatLevel(terms: Seq[NameType]): (Int, Seq[(Name, Boolean, Abstract.MetaEnclosed)]) = {
    var ctx = newParametersLayer()
    var l = 0
    val fas = terms.flatMap(f => {
      val fs = NameType.flatten(Seq(f))
      if (fs.map(_._2).toSet.size != fs.size) {
        throw ElaborateException.AlreadyDeclared()
      }
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


  private def inferTelescope(domain: NameType.FlatSeq, codomain: Option[Concrete], body: Concrete): (Abstract, Abstract) = {
    domain match {
      case head +: tail =>
        head._3 match {
          case Concrete.I =>
            if (head._1) throw ElaborateException.DimensionLambdaCannotBeImplicit()
            val ctx = newDimensionLayer(head._2)._1
            val (ta, va) = ctx.inferTelescope(tail, codomain, body)
            val ms = ctx.finishReify()
            val cloa = Abstract.AbsClosure(ms, va)
            val clov = eval(cloa)
            val left = clov(Value.Dimension.False)
            val right = clov(Value.Dimension.True)
            (Abstract.PathType(Abstract.AbsClosure(ms, ta), reify(left), reify(right)), Abstract.PathLambda(cloa))
          case _ =>
            val (_, da) = inferLevel(head._3)
            val ctx = newParameterLayer(head._2, eval(da))._1
            val (ta, va) = ctx.inferTelescope(tail, codomain, body)
            val ms = ctx.finishReify()
            (Abstract.Function(da, head._1, Abstract.Closure(ms, ta)), Abstract.Lambda(Abstract.Closure(ms, va)))
        }
      case Seq() =>
        codomain match {
          case Some(value) =>
            val (_, a) = inferLevel(value)
            (a, check(body, eval(a)))
          case None =>
            val (bt, ba) = infer(body)
            val btr = reify(bt)
            debug(s"infer domain $btr", 1)
            (btr, ba)
        }
    }
  }

  private def inferTelescope(domain: NameType.FlatSeq, codomain: Concrete): (Int, Abstract) = {
    domain match {
      case head +: tail =>
        head._3 match {
          case Concrete.I =>
            throw ElaborateException.CannotInferPathTypeWithoutBody()
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

  private def inferApp(lt: Value, la: Abstract, arguments: Seq[(Boolean, Concrete)]): (Value, Abstract) = {
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
              throw ElaborateException.NotExpectingImplicitArgument()
            }
          case Value.PathType(typ, _, _) =>
            if (head._1) throw ElaborateException.DimensionLambdaCannotBeImplicit()
            val (dv, da) = checkDimension(head._2)
            val lt1 = typ(dv)
            val la1 = Abstract.PathApp(la, da)
            inferApp(lt1, la1, tail)
          // TODO user defined applications
          case _ => throw ElaborateException.UnknownAsFunction()
        }
      case Seq() =>
        (lt, la)
    }
  }

  private def check(
                     term: Concrete,
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
        case Concrete.Hole =>
          newMeta(cp)._2
        case _ =>
          val (tt, ta) = infer(term)
          if (subTypeOf(tt, cp)) ta
          else {
            info(s"${reify(tt.whnf)}")
            info(s"${reify(cp.whnf)}")
            throw ElaborateException.TypeMismatch()
          }
      }
    }
    cp.whnf match {
      case Value.Function(domain, fimp, codomain) =>
        term match {
          case Concrete.Lambda(n, limp, body) if fimp == limp =>
            val (ctx, v) = newParameterLayer(n.nonEmptyOrElse(hint), domain)
            val ba = ctx.check(body, codomain(v), tail)
            Abstract.Lambda(Abstract.Closure(ctx.finishReify(), ba))
          case Concrete.PatternLambda(limp, cases) if fimp == limp =>
            val res = cases.map(c => {
              val (ctx, v, pat) = newPatternLayer(c.pattern, domain)
              val ba = ctx.check(c.body, codomain(v), tail)
              Abstract.Case(pat, Abstract.MultiClosure(ctx.finishReify(), ba))
            })
            Abstract.PatternLambda(Elaborator.pgen(), reify(domain), reify(codomain), res)
          case _ =>
            if (fimp) {
              val (ctx, v) = newParameterLayer(Name.empty, domain)
              val ba = ctx.check(term, codomain(v), tail)
              Abstract.Lambda(Abstract.Closure(ctx.finishReify(), ba))
            } else {
              fallback()
            }
        }
      case Value.VType(x, a, b, e) =>
//        term match {
//          case Concrete.VMake(tm, tn) =>
//            val dp = Value.DimensionPair(x, Value.Dimension.False)
//            val ctxr = newRestrictionLayer(dp)
//            val m0 = ctxr.check(tm, a)
//            val m = Abstract.MetaEnclosed(ctxr.finishReify(), m0)
//            val n = check(tn, b)
//            if (ctxr.unifyTerm(b.restrict(dp), Value.App(Value.Projection(e, 0), ctxr.eval(m0)), eval(n).restrict(dp))) {
//              Abstract.VMake(rebindDimension(x), m, n)
//            } else {
//              throw TypeCheckException.VMakeMismatch()
//            }
//          case _ => fallback()
//        }
        ???
      case Value.PathType(typ, left, right) =>
        term match {
          case Concrete.Lambda(n, b, body) =>
            if (b) throw ElaborateException.DimensionLambdaCannotBeImplicit()
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
              throw ElaborateException.PathEndPointsNotMatching()
            }
          case _ => fallback()
        }
      case r: Value.Record =>
        val cpd = reify(cp)
        debug(s"reified record make type $cpd", 1)
        term match {
          case Concrete.App(Concrete.Make, vs) =>
            inferApp(r.makerType, Abstract.Maker(cpd, -1), vs)._2
          case Concrete.Let(declarations, Concrete.App(Concrete.Make, vs)) =>
            val (ctx, ms, da) = newDefinesLayer().checkDeclarations(declarations, false)
            val ia= ctx.inferApp(r.makerType, Abstract.Maker(cpd, -1), vs)._2
            val ms0 = ctx.freezeReify()
            Abstract.Let(ms ++ ms0, da, ia)
          case _ =>
            fallback()
        }
      case _ => fallback()
    }
  }

  // FIXME consider use a different setup for global identifiers, so we can implement up only in abstract layer
  // FIXME also maybe each reference should have a "support" so do less restrictions
  // FIXME can you recur inside a up or restriction? a way to disallow this is to make sure all recursive reference doesn't happens under a restriction/lift
  private def checkDeclaration(
      s: Declaration,
      mis: mutable.ArrayBuffer[CodeInfo[Value.Meta]],
      vis: mutable.ArrayBuffer[DefinitionInfo], topLevel: Boolean): Self = {
    def wrapBody(t: Concrete, imp: Seq[Boolean]): Concrete = if (imp.isEmpty) t else wrapBody(Concrete.Lambda(Name.empty, imp.last, t), imp.dropRight(1))
    def appendMetas(ms: Seq[Value.Meta]): Unit = {
      for (m <- ms) {
        mis.append(CodeInfo(reify(m.solved), m))
      }
    }
    def reevalStuff(ctx: Elaborator, changed: Dependency): Unit = {
      val done = mutable.ArrayBuffer.empty[Dependency]
      // the reason it needs to rec, is that we have whnf remembered
      def rec(c: Dependency): Unit = {
        done.append(c)
        for (i <- mis.indices) {
          val m = mis(i)
          val handle = Dependency(i, true)
          if (!done.contains(handle) && m.dependencies.contains(changed)) {
            m.t.state = Value.Meta.Closed(ctx.eval(m.code))
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
        var inductively: Option[Long] =
          if (ms.contains(Modifier.Inductively)) {
            if (topLevel) {
              Some(Elaborator.igen())
            } else {
              throw ElaborateException.RecursiveTypesMustBeDefinedAtTopLevel()
            }
          } else None
        val ret = lookupDefined(name) match {
          case Some((index, typ, defined)) =>
            if (defined) {
              throw ElaborateException.AlreadyDefined()
            }
            info(s"check defined $name")
            if (ps.nonEmpty || t0.nonEmpty) throw ElaborateException.SeparateDefinitionCannotHaveTypesNow()
            val va = check(v, typ, Seq.empty)
            appendMetas(freeze())
            val ref = Value.Reference(null)
            val ctx = newDefinitionChecked(index, name, ref)
            ref.value = ctx.eval(va)
            vis(index).code = Some(CodeInfo(va, ref))
            reevalStuff(ctx, Dependency(index, false))
            info(s"checked $name")
            ctx
          case None => t0 match {
            case Some(t) if !ps.exists(_.ty == Concrete.I) =>
              // term with type
              info(s"define $name")
              val pps = NameType.flatten(ps)
              val (_, ta) = inferTelescope(pps, t)
              appendMetas(freeze())
              val tv = eval(ta)
              val (ctx, index, generic) = newDeclaration(name, tv) // allows recursive definitions
              fillTo(vis, index); assert(vis(index) == null)
              vis.update(index, DefinitionInfo(None, CodeInfo(ta, generic)))
              val lambdaNameHints = pps.map(_._2) ++ (t match {
                case Concrete.Function(d, _) =>
                  NameType.flatten(d).map(_._2)
                case _ => Seq.empty
              })
              val va0 = ctx.check(wrapBody(v, pps.map(_._1)), tv, lambdaNameHints)
              val va = if (inductively.isDefined) {
                if (pps.nonEmpty) {
                  warn("we don't support parameterized inductive type yet")
                  ???
                }
                val level = tv.whnf.asInstanceOf[Value.Universe].level
                val tt = Some(Abstract.Inductively(inductively.get, level))
                va0 match {
                  case s: Abstract.Sum => inductively = None; assert(s.inductively.isEmpty); s.copy(inductively = tt)
                  case s: Abstract.Record => inductively = None; assert(s.inductively.isEmpty); s.copy(inductively = tt)
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

              // some definition is specially treated, they are defined in code, but we need to reference them in evaluator.
              // these definition should not have re-eval behaviour.
              // TODO add a primitive modifier so that no error happens with this
              if (name == Name(Text("fiber_at"))) {
                assert(Value.fiber_at == null)
                Value.fiber_at = ref.value
                Value.fiber_at_ty = tv
              } else if (name == Name(Text("equiv"))) {
                assert(Value.equiv == null)
                Value.equiv = ref.value
              }
              info(s"defined $name")
              ctx2
            case _ =>
              // term without type
              info(s"infer $name")
              val (ta, va) = inferTelescope(NameType.flatten(ps), t0, v)
              appendMetas(freeze())
              val ref = Value.Reference(eval(va))
              val (ctx, index, generic) = newDefinition(name, eval(ta), ref)
              fillTo(vis, index); assert(vis(index) == null)
              vis.update(index, DefinitionInfo(Some(CodeInfo(va, ref)), CodeInfo(ta, generic)))
              info(s"inferred $name")
              ctx
          }
        }
        if (inductively.isDefined) warn(s"${name.toString} is not a inductive type but has modifier inductively")
        ret
      case Declaration.Declare(ms, name, ps, t) =>
        lookupDefined(name) match {
          case Some(_) =>
            throw ElaborateException.AlreadyDeclared()
          case None =>
            info(s"declare $name")
            if (ms.exists(_ != Modifier.__Debug)) throw ElaborateException.ForbiddenModifier()
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
  }

  private def checkDeclarations(seq: Seq[Declaration], topLevel: Boolean): (Self, Seq[Abstract], Seq[Abstract]) = {
    // how to handle mutual recursive definitions, calculate strong components
    var ctx = this
    val ms = mutable.ArrayBuffer.empty[CodeInfo[Value.Meta]]
    val vs = mutable.ArrayBuffer.empty[DefinitionInfo]

    // this is a TOTAL hack because we don't have modules yet
    val __t = Abstract.Universe(0)
    for (_ <- 0 until layers.head.metas.size) {
      ms.append(CodeInfo(__t, null))
    }
    for (_ <- layers.head.asInstanceOf[Layer.Defines].terms) {
      vs.append(DefinitionInfo(Some(CodeInfo(__t, null)), CodeInfo(__t, null)))
    }

    for (s <- seq) {
      val ctx0 = ctx.checkDeclaration(s, ms, vs, topLevel)
      ctx = ctx0
    }
    if (vs.exists(a => a.code.isEmpty)) {
      throw ElaborateException.DeclarationWithoutDefinition()
    }
    (ctx, ms.map(_.code).toSeq, vs.map(_.code.get.code).toSeq)
  }



  private def inferLevel(term: Concrete): (Int, Abstract) = {
    val (tt, ta) = infer(term)
    tt.whnf match {
      case Value.Universe(l) => (l, ta)
      // TODO user defined type coercion
      case _ => throw ElaborateException.UnknownAsType()
    }
  }


  def check(m: Module): Elaborator = Benchmark.TypeChecking {
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





