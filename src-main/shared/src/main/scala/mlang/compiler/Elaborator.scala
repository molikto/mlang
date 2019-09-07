package mlang.compiler

import mlang.compiler.Concrete._
import Declaration.Modifier
import mlang.compiler.Layer.Layers
import mlang.utils._

import scala.collection.mutable
import scala.language.implicitConversions



object Elaborator {
  private val pgen = new LongGen.Positive()
  private val igen = new LongGen.Positive()
  def topLevel(): Elaborator = new Elaborator(Seq.empty).newDefinesLayer()
}

// TODO because these are mutational code (see Readme about meta), reread these so no errors
class Elaborator private(protected override val layers: Layers)
    extends ElaboratorContextBuilder
        with ElaboratorContextLookup
        with ElaboratorContextRebind
        with ElaboratorContextForEvaluator
        with Evaluator with PlatformEvaluator with Unifier {

  override type Self = Elaborator

  override protected implicit def create(a: Layers): Self = new Elaborator(a)

  def doForValidFormulaOrThrow[T](f: Value.Formula, a: Value.Formula.Assignments => T): T = {
    val davn = f.normalForm
    val valid = davn.filter(Value.Formula.Assignments.satisfiable)
    if (valid.isEmpty) {
      throw ElaboratorException.RemoveStaticFalseOrUnsatisfiableFace()
    } else {
      if (valid.size > 1) throw ElaboratorException.StaticDisjunctionCurrentlyNotSupported()
      a(valid.head)
    }
  }

  def checkCompatibleCapAndFaces(
                                  faces: Seq[Concrete.Face],
                                  bt: Value.AbsClosure,
                                  bv: Value
  ): Seq[Abstract.Face] = {
    import Value.Formula
    val nfs = mutable.ArrayBuffer.empty[Value.Formula.Assignments]
    val tms = mutable.ArrayBuffer.empty[Value]
    faces.indices.map { i =>
      val a = faces(i)
      val (dav, daa) = checkAndEvalFormula(a.dimension)
      doForValidFormulaOrThrow(dav, asgn0 => {
        nfs.append(asgn0)
        val ctx0 = newSyntaxDirectedRestrictionLayer(asgn0)
        val btr = bt.restrict(asgn0)
        // FIXME no hurry to finalize this context? use information in cap to infer?
        val (dim, na) = ctx0.checkLine(a.term, btr)
        val naa = ctx0.eval(na)
        val nv = naa(Formula.False)
        tms.append(nv)
        if (!ctx0.unifyTerm(btr(dim), bv.restrict(asgn0), nv)) { // nv.restrict(asgn0)
          throw ElaboratorException.CapNotMatching()
        }
        for (j <- 0 until i) {
          val asgn1 = nfs(j)
          // this might evaluate the dimensions to new values
          val dfv = asgn1 ++ asgn0
          // only used to test if this restriction is false face or not
          if (Value.Formula.Assignments.satisfiable(dfv)) {
            val ctx0 = newSyntaxDirectedRestrictionLayer(dfv)
            val (ctx1, dim) = ctx0.newDimensionLayer(Name.empty)
            if (!ctx1.unifyTerm(
              btr(dim).restrict(dfv),
              nv.restrict(dfv),
              tms(j).restrict(dfv))) {
              throw ElaboratorException.FacesNotMatching()
            }
          }
        }
        Abstract.Face(daa, na)
      })
    }
  }


  def checkLine(a: Concrete, typ: Value.AbsClosure): (Value.Formula.Generic, Abstract.AbsClosure) = {
    a match {
      case Concrete.Lambda(n, b, _, body) =>
        if (b) throw ElaboratorException.DimensionLambdaCannotBeImplicit()
        val (ctx, dim) = newDimensionLayer(n)
        val ta = ctx.check(body, typ(dim))
        (dim, Abstract.AbsClosure(ctx.finishReify(), ta))
      case _ =>
        val (ctx, dim) = newDimensionLayer(Name.empty) // it is ok to infer in this context, as the name is empty so it doesn't affect much
        val (tv, ta) = ctx.infer(a)
        tv.whnf match {
          case j@Value.PathType(_, _, _) =>
            (dim, Abstract.AbsClosure(ctx.finishReify(), Abstract.PathApp(ta, Abstract.Formula.Reference(0))))
          case _ => throw ElaboratorException.ExpectingLambdaTerm()
        }
    }
  }
  def checkTypeLine(a: Concrete): (Int, Abstract.AbsClosure) = {
    a match {
      case Concrete.Lambda(n, b, _, body) =>
        if (b) throw ElaboratorException.DimensionLambdaCannotBeImplicit()
        val ctx = newDimensionLayer(n)._1
        val (l, ta0) = ctx.inferLevel(body)
        val ta = Abstract.AbsClosure(ctx.finishReify(), ta0)
        (l, ta)
      case _ =>
        val ctx = newDimensionLayer(Name.empty)._1
        val (tv, ta) = ctx.infer(a)
        tv.whnf match {
          case j@Value.PathType(_, _, _) =>
            val clo = Abstract.AbsClosure(ctx.finishReify(), Abstract.PathApp(ta, Abstract.Formula.Reference(0)))
            (j.inferLevel, clo)
          case _ => throw ElaboratorException.ExpectingLambdaTerm()
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
            (Value.Universe.suc(b + 1), Abstract.Universe(if (Value.Universe.TypeInType) 0 else b))
          case Concrete.Reference(ref) =>
            val (binder, abs) = lookupTerm(ref)
            abs match {
              case Abstract.Reference(up, _) if up == layers.size - 1 =>
              reduceMore(binder, abs)
              //reduceMore(binder.up(b), Abstract.Up(abs, b))
              case _ => throw ElaboratorException.UpCanOnlyBeUsedOnTopLevelDefinitionOrUniverse()
            }
          case _ => throw ElaboratorException.UpCanOnlyBeUsedOnTopLevelDefinitionOrUniverse()
        }
      case Concrete.Reference(name) =>
        // should lookup always return a value? like a open reference?
        val (binder, abs) = lookupTerm(name)
        reduceMore(binder, abs)
      case Concrete.Hole =>
        throw ElaboratorException.CannotInferMeta()
      case Concrete.True =>
        throw ElaboratorException.ConstantSortWrong()
      case Concrete.False =>
        throw ElaboratorException.ConstantSortWrong()
        // LATER these three is not exactly constants, maybe this can be fixed after refactor better elaboration
      case _: Concrete.And =>
        throw ElaboratorException.ConstantSortWrong()
      case _: Concrete.Or =>
        throw ElaboratorException.ConstantSortWrong()
      case _: Concrete.Neg =>
        throw ElaboratorException.ConstantSortWrong()
      case Concrete.I =>
        throw ElaboratorException.TermICanOnlyAppearInDomainOfFunction()
      case Concrete.Make =>
        throw ElaboratorException.CannotInferMakeExpression()
      case _: Concrete.Glue =>
        throw ElaboratorException.CannotInferVMakeExpression()
      case Concrete.Cast(v, t) =>
        val (_, ta) = inferLevel(t)
        val tv = eval(ta)
        (tv, check(v, tv))
      case Concrete.Function(domain, codomain) =>
        if (domain.isEmpty) throw ElaboratorException.EmptyTelescope()
        val (l, v) = inferTelescope(NameType.flatten(domain), codomain)
        (Value.Universe(l), v)
      case r@Concrete.Record(fields) =>
        for (f <- fields) {
          if (f.names.isEmpty) throw ElaboratorException.MustBeNamed()
        }
        for (i <- r.names.indices) {
          for (j <- (i + 1) until r.names.size) {
            if (r.names(i)._2 intersect r.names(j)._2) {
              throw ElaboratorException.FieldsDuplicated()
            }
          }
        }
        val (fl, fs) = newLayerInferFlatLevel(fields)
        (Value.Universe(fl), Abstract.Record(None, fs.map(_._1), fs.map(_._2), fs.map(a => (a._3.term.termDependencies(0).toSeq.sorted, a._3))))
      case Concrete.Sum(constructors) =>
        for (i <- constructors.indices) {
          for (j <- (i + 1) until constructors.size) {
            if (constructors(i).name.intersect(constructors(j).name)) {
              throw ElaboratorException.TagsDuplicated()
            }
          }
        }
        // TODO in case of HIT, each time a constructor finished, we need to construct a partial sum and update the value
        val fs = constructors.map(c => newLayerInferFlatLevel(c.term))
        val fl = fs.map(_._1).max
        (Value.Universe(fl), Abstract.Sum(None, fs.map(_._2).zip(constructors).map(a =>
          Abstract.Constructor(a._2.name, a._1.map(k => k._2), a._1.zipWithIndex.map(kk => (0 until kk._2, kk._1._3))))))
      case Concrete.Transp(tp, direction, base) =>
        // LATER does these needs finish off implicits?
        val (dv, da) = checkAndEvalFormula(direction)
        val (tv, ta) = checkTypeLine(tp)
        val cl = eval(ta)
        val (ctx, dim) = newDimensionLayer(Name.empty)
        val constant = dv.normalForm.filter(a => Value.Formula.Assignments.satisfiable(a)).forall(asg => {
          ctx.newSyntaxDirectedRestrictionLayer(asg).unifyTerm(Value.Universe(tv), cl(dim).restrict(asg), cl(Value.Formula.False).restrict(asg))
        })
        if (!constant) {
          throw ElaboratorException.TranspShouldBeConstantOn()
        }
        val ba = check(base, cl(Value.Formula.False))
        (cl(Value.Formula.True), Abstract.Transp(ta, da, ba))
      case Concrete.Com(tp, base, faces) =>
        val (_, ta) = checkTypeLine(tp)
        val cl = eval(ta)
        val ba = check(base, cl(Value.Formula.False))
        val rs = checkCompatibleCapAndFaces(faces, cl, eval(ba))
        (cl(Value.Formula.True), Abstract.Com(ta, ba, rs))
      case Concrete.Hcom(base, faces) =>
        val (bt, ba) = infer(base)
        val bv = eval(ba)
        val rs = checkCompatibleCapAndFaces(faces, Value.AbsClosure(bt), bv)
        val btr = reify(bt)
        debug(s"infer hcom type $btr", 1)
        (bt, Abstract.Hcom(btr, ba, rs))
      case Concrete.PathType(typ, left, right) =>
        typ match {
          case Some(tp) =>
            val (tl, ca) = checkTypeLine(tp)
            val tv = eval(ca)
            val la = check(left, tv(Value.Formula.False))
            val ra = check(right, tv(Value.Formula.True))
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
                debug(s"infer path type $ta", 0)
                (Value.Universe(t.inferLevel), Abstract.PathType(Abstract.AbsClosure(Seq.empty, ta), la, ra))
              case None =>
                throw ElaboratorException.InferPathEndPointsTypeNotMatching()
            }
        }
      case p: Concrete.PatternLambda =>
        throw ElaboratorException.CannotInferReturningTypeWithPatterns()
      case l: Concrete.Lambda =>
        if (l.ensuredPath) {
          assert(!l.imps)
          val (ta, va) = inferTelescope(Seq((false, l.name, Concrete.I)), None, l.body)
          (eval(ta), va)
        } else {
          throw ElaboratorException.CannotInferLambda()
        }
      case Concrete.Projection(left, right) =>
        val (lt, la) = infer(left)
        val lv = eval(la)
        lazy val ltr = lt.whnf.asInstanceOf[Value.Record]
        def error() = throw ElaboratorException.UnknownProjection()
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
        if (arguments.isEmpty) throw ElaboratorException.EmptyArguments()
        val (lt, la) = infer(lambda, true)
        val (v1, v2) = inferApp(lt, la, arguments)
        reduceMore(v1, v2) // because inferApp stops when arguments is finished
      case Concrete.GlueType(ty, faces) =>
        val (lv, ta) = inferLevel(ty)
        val tv = eval(ta)
        val facesA = faces.map(f => {
          val formula = checkAndEvalFormula(f.dimension)
          val ba = doForValidFormulaOrThrow(formula._1, asgn => {
            val ctx = newDimensionLayer(Name.empty)._1 // this is currently a hack!
            // TODO here we checked by same level as ty.
            val bd = ctx.check(f.term, Value.App(BuiltIn.equiv_of, tv).restrict(asgn))
            Abstract.AbsClosure(ctx.finishReify(), bd)
          })
          Abstract.Face(formula._2, ba)
        })
        (Value.Universe(lv), Abstract.GlueType(ta, facesA))
      case Concrete.Unglue(m) =>
        val (mt, ma) = infer(m)
        mt.whnf match {
          case Value.GlueType(ty, faces) =>
            (ty, Abstract.Unglue(reify(ty), ma, reifyFaces(faces)))
          case _ => throw ElaboratorException.UnglueCannotInfer()
        }
      case Concrete.Let(declarations, in) =>
        val (ctx, ms, da) = newDefinesLayer().checkDeclarations(declarations, false)
        val (it, ia) = ctx.infer(in)
        val ms0 = ctx.freezeReify()
        (it, Abstract.Let(ms ++ ms0, da, ia))
    }
    debug(s"infer result ${res._2}")
    res
  }

  private def checkAndEvalFormula(r: Concrete): (Value.Formula, Abstract.Formula) = {
    val a = checkFormula(r)
    (eval(a), a)
  }
  // it always returns formulas with assignments inlined
  private def checkFormula(r: Concrete): Abstract.Formula = {
    r match {
      case Concrete.Reference(name) =>
         lookupDimension(name)
      case Concrete.And(left, right) =>
        val l = checkFormula(left)
        val r = checkFormula(right)
        Abstract.Formula.And(l, r)
      case Concrete.Or(left, right) =>
        val l = checkFormula(left)
        val r = checkFormula(right)
        Abstract.Formula.Or(l, r)
      case Concrete.Neg(a) =>
        val r = checkFormula(a)
        Abstract.Formula.Neg(r)
      case Concrete.True =>
        Abstract.Formula.True
      case Concrete.False =>
        Abstract.Formula.False
      case _ => throw ElaboratorException.ExpectingFormula()
    }
  }

  private def newLayerInferFlatLevel(terms: Seq[NameType]): (Int, Seq[(Name, Boolean, Abstract.MetaEnclosed)]) = {
    var ctx = newParametersLayer()
    var l = 0
    val fas = terms.flatMap(f => {
      val fs = NameType.flatten(Seq(f))
      if (fs.map(_._2).toSet.size != fs.size) {
        throw ElaboratorException.AlreadyDeclared()
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
            if (head._1) throw ElaboratorException.DimensionLambdaCannotBeImplicit()
            val ctx = newDimensionLayer(head._2)._1
            val (ta, va) = ctx.inferTelescope(tail, codomain, body)
            val ms = ctx.finishReify()
            val cloa = Abstract.AbsClosure(ms, va)
            val clov = eval(cloa)
            val left = clov(Value.Formula.False)
            val right = clov(Value.Formula.True)
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
            throw ElaboratorException.CannotInferPathTypeWithoutBody()
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
              throw ElaboratorException.NotExpectingImplicitArgument()
            }
          case Value.PathType(typ, _, _) =>
            if (head._1) throw ElaboratorException.DimensionLambdaCannotBeImplicit()
            val da = checkFormula(head._2)
            val lt1 = typ(eval(da))
            val la1 = Abstract.PathApp(la, da)
            inferApp(lt1, la1, tail)
          // TODO user defined applications
          case _ =>
            throw ElaboratorException.UnknownAsFunction()
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
            if (debug.enabled) {
              val ignore = subTypeOf(tt, cp)
            }
            throw ElaboratorException.TypeMismatch()
          }
      }
    }
    cp.whnf match {
      case Value.Function(domain, fimp, codomain) =>
        term match {
          case Concrete.Lambda(n, limp, ensuredPath, body) if fimp == limp =>
            assert(!ensuredPath)
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
      case Value.GlueType(ty, faces) =>
        term match {
          case Concrete.Glue(base, fs) =>
            val ba = check(base, ty)
            val bv = eval(ba)
            val phi1 = faces.flatMap(_.restriction.normalForm).toSet
            val ffs = fs.map(a => { val (f1, f2) = checkAndEvalFormula(a.dimension); (f1, f2, a.term) })
            val phi2 = ffs.flatMap(_._1.normalForm).toSet
            if (phi1 == phi2) {
              val fas = ffs.map(f => {
                val body = doForValidFormulaOrThrow(f._1, asgn => {
                  val terms = mutable.Set.empty[Abstract.AbsClosure]
                  for (tf <- faces) {
                    tf.restriction.normalForm.filter(Value.Formula.Assignments.satisfiable).foreach(asgn2 => {
                      val asg = asgn ++ asgn2
                      if (Value.Formula.Assignments.satisfiable(asg)) {
                        val ctx = newSyntaxDirectedRestrictionLayer(asg).newDimensionLayer(Name.empty)._1
                        val bd1 = tf.body(Value.Formula.Generic.HACK).restrict(asg)
                        val res = ctx.check(f._3, Value.Projection(bd1, 0))
                        val itemv = eval(res)
                        if (ctx.unifyTerm(ty.restrict(asg), bv.restrict(asg), Value.App(Value.Projection(bd1, 1), itemv))) {
                          terms.add(Abstract.AbsClosure(ctx.finishReify(), res))
                        } else {
                          throw ElaboratorException.GlueNotMatching()
                        }
                      }
                    })
                  }
                  if (terms.size != 1) {
                    logicError()
                  }
                  terms.head
                })
                Abstract.Face(f._2, body)
              })
              Abstract.Glue(ba, fas)
            } else {
              throw ElaboratorException.FacesNotMatching()
            }
          case _ => fallback()
        }
      case Value.PathType(typ, left, right) =>
        term match {
          case Concrete.Lambda(n, b, _, body) =>
            if (b) throw ElaboratorException.DimensionLambdaCannotBeImplicit()
            val (c1, dv) = newDimensionLayer(n.nonEmptyOrElse(hint))
            val t1 = typ(dv)
            import Value.Formula._
            val a1 = c1.check(body, t1, tail)
            val ps = Abstract.AbsClosure(c1.finishReify(), a1)
            val pv = eval(ps)
            val leftEq = unifyTerm(typ(False), pv(False), left)
            val rightEq = unifyTerm(typ(True), pv(True), right)
            if (leftEq && rightEq) {
              Abstract.PathLambda(ps)
            } else {
              throw ElaboratorException.PathEndPointsNotMatching()
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

  private def newReference(v: Value = null): Value.Reference = if (layers.size == 1) Value.GlobalReference(v) else Value.LocalReference(v)

  // FIXME should we make sure type annotation is the minimal type?
  private def checkDeclaration(
      s: Declaration,
      mis: mutable.ArrayBuffer[CodeInfo[Value.Meta]],
      vis: mutable.ArrayBuffer[DefinitionInfo], topLevel: Boolean): Self = {
    def wrapBody(t: Concrete, imp: Seq[Boolean]): Concrete = if (imp.isEmpty) t else wrapBody(Concrete.Lambda(Name.empty, imp.last, false, t), imp.dropRight(1))
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
            m.t.state = Value.MetaState.Closed(ctx.eval(m.code))
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
              throw ElaboratorException.RecursiveTypesMustBeDefinedAtTopLevel()
            }
          } else None
        val ret = lookupDefined(name) match {
          case Some((index, typ, defined)) =>
            if (defined) {
              throw ElaboratorException.AlreadyDefined()
            }
            info(s"check defined $name")
            if (ps.nonEmpty || t0.nonEmpty) throw ElaboratorException.SeparateDefinitionCannotHaveTypesNow()
            val va = check(v, typ, Seq.empty)
            appendMetas(freeze())
            val ref = newReference()
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
              val ref = newReference()
              val ctx2 = ctx.newDefinitionChecked(index, name, ref)
              ref.value = ctx2.eval(va) // we want to eval it under the context with reference to itself
              vis(index).code = Some(CodeInfo(va, ref))
              // you don't need to reevaluate stuff here, no one reference me now!

              // some definition is specially treated, they are defined in code, but we need to reference them in evaluator.
              // these definition should not have re-eval behaviour.
              // TODO add a primitive modifier so that no error happens with this
              if (name == Name(Text("fiber_at"))) {
                assert(BuiltIn.fiber_at == null)
                BuiltIn.fiber_at = ref.value
                BuiltIn.fiber_at_ty = tv
              } else if (name == Name(Text("equiv"))) {
                assert(BuiltIn.equiv == null)
                BuiltIn.equiv = ref.value
              } else if (name == Name(Text("equiv_of"))) {
                assert(BuiltIn.equiv_of == null)
                BuiltIn.equiv_of = ref.value
              }
              info(s"defined $name")
              ctx2
            case _ =>
              // term without type
              info(s"infer $name")
              val (ta, va) = inferTelescope(NameType.flatten(ps), t0, v)
              appendMetas(freeze())
              val ref = newReference(eval(va))
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
            throw ElaboratorException.AlreadyDeclared()
          case None =>
            info(s"declare $name")
            if (ms.exists(_ != Modifier.__Debug)) throw ElaboratorException.ForbiddenModifier()
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
      throw ElaboratorException.DeclarationWithoutDefinition()
    }
    (ctx, ms.map(_.code).toSeq, vs.map(_.code.get.code).toSeq)
  }



  private def inferLevel(term: Concrete): (Int, Abstract) = {
    val (tt, ta) = infer(term)
    tt.whnf match {
      case Value.Universe(l) => (l, ta)
      // TODO user defined type coercion
      case _ => throw ElaboratorException.UnknownAsType()
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


