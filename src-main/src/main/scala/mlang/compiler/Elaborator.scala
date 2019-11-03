package mlang.compiler

import mlang.compiler.Concrete._
import Declaration.Modifier
import mlang.compiler.Abstract.{Inductively, MetaEnclosed}
import mlang.compiler.Layer.Layers
import mlang.compiler.Value.{ClosureGraph, PathLambda, PatternRedux, StableCanonical, UnstableCanonical}
import mlang.utils._

import scala.annotation.Annotation
import scala.collection.mutable
import scala.language.implicitConversions
import scala.util.Random

class syntax_creation extends Annotation

private class IndState(val id: Long, typ: Abstract, var stop: Boolean, var top: Value, var apps: Seq[Value] = Seq.empty) {
  // returns a value is self
  def consume(level: Int): Option[(Value, Abstract.Inductively)] = {
    if (stop) {
      None
    } else {
      val ret = Abstract.Inductively(id, typ, (0 until apps.size).map(i => Abstract.Reference(i, -1)).reverse)
      stop = true
      Some((Value.Apps(top, apps), ret))
    }
  }


  def app(v: Value): IndState = {
    if (stop) this else {
      apps = apps :+ v
      this
    }
  }

}

private object IndState {
  val stop = new IndState(0, null, true, null)
}

object Elaborator {
  private val pgen = new GenLong.Positive()
  private val igen = new GenLong.Positive()
  def topLevel(): Elaborator = new Elaborator(Seq.empty).newDefinesLayer()
}

// TODO because these are mutational code (see Readme about meta), reread these so no errors
// TODO there are some marked as "syntax_creation" which modify concrete syntax directly, and this is unwanted
class Elaborator private(protected override val layers: Layers)
    extends ElaboratorContextBuilder
        with ElaboratorContextLookup
        with ElaboratorContextRebind
        with ElaboratorContextForEvaluator
        with DebugPrettyPrinter
        with Evaluator with PlatformEvaluator with MetaSolver {


  override type Self = Elaborator
  override protected implicit def create(a: Layers): Self = new Elaborator(a)

  private def doForValidFormulaOrThrow[T](f: semantic.Formula, a: semantic.Formula.Assignments => T): T = {
    val davn = f.normalForm
    val valid = davn.filter(semantic.Formula.Assignments.satisfiable)
    if (valid.isEmpty) {
      throw ElaboratorException.RemoveStaticFalseOrUnsatisfiableFace()
    } else {
      if (valid.size > 1) throw ElaboratorException.StaticDisjunctionCurrentlyNotSupported()
      a(valid.head)
    }
  }

  private def checkCompatibleCapAndFaces(
                                  faces: Seq[Concrete.Face],
                                  bt: Value.AbsClosure,
                                  bv: Value
  ): Abstract.AbsClosureSystem = {
    import semantic.Formula
    val nfs = mutable.ArrayBuffer.empty[semantic.Formula.Assignments]
    val tms = mutable.ArrayBuffer.empty[Value]
    faces.indices.map { i =>
      val a = faces(i)
      val (dav, daa) = checkAndEvalFormula(a.dimension)
      doForValidFormulaOrThrow(dav, asgn0 => {
        nfs.append(asgn0)
        val ctx0 = newSyntaxDirectedRestrictionLayer(asgn0)
        val btr = bt.restrict(asgn0)
        // FIXME(META) no hurry to finalize this context? use information in cap to infer?
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
          if (semantic.Formula.Assignments.satisfiable(dfv)) {
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
        (daa, na)
      })
    }.toMap
  }


  private def checkLine(a: Concrete, typ: Value.AbsClosure): (semantic.Formula.Generic, Abstract.AbsClosure) = {
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
            (dim, Abstract.AbsClosure(ctx.finishReify(), Abstract.PathApp(ta, Abstract.Formula.Reference(0, -1))))
          case _ => throw ElaboratorException.ExpectingLambdaTerm()
        }
    }
  }

  private def checkTypeLine(a: Concrete): (Int, Abstract.AbsClosure) = {
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
            val clo = Abstract.AbsClosure(ctx.finishReify(), Abstract.PathApp(ta, Abstract.Formula.Reference(0, -1)))
            (j.inferLevel, clo)
          case _ => throw ElaboratorException.ExpectingLambdaTerm()
        }
    }
  }

  @scala.annotation.tailrec
  private def finishOffImplicits(v: Value, abs: Abstract): (Value, Abstract) = {
    v.whnf match {
      case Value.Function(d, i, c) if i =>
        val (mv, ma) = newMeta(d)
        finishOffImplicits(c(mv), Abstract.App(abs, ma))
      case _ => (v, abs)
    }
  }


  def checkRecord(ind: Option[Abstract.Inductively], r: Concrete.Record): (Value, Abstract) = {
    val Concrete.Record(fields) = r
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
    val ctx = newParametersLayer()
    val (fl, fs, _) = ctx.inferFlatLevel(NameType.flatten(fields))
    (Value.Universe(fl), Abstract.Record(
      ind,
      fs.map(_._1),
      Abstract.ClosureGraph(fs.map(a => Abstract.ClosureGraph.Node(a._2, a._3.term.termDependencies(0).toSeq.sorted, a._3)))))
  }

  def checkSum(tps: Option[(Value, Option[(Value, Abstract.Inductively)], Int)], sum: Concrete.Sum): (Value, Abstract) = {
    val Concrete.Sum(constructors) = sum
    for (i <- constructors.indices) {
      for (j <- (i + 1) until constructors.size) {
        if (constructors(i).name.intersect(constructors(j).name)) {
          throw ElaboratorException.TagsDuplicated()
        }
      }
    }
    val selfValue = tps.map(pair => {
      pair._2.map(_._1).getOrElse(Value.Generic(ElaboratorContextBuilder.gen(), pair._1))
    })
    var ctx = newParametersLayer(selfValue)
    var isHit = false
    val fs = constructors.map(c => {
      val seq = NameType.flatten(c.term)
      val tpd = seq.takeWhile(_._3 != Concrete.I)
      val is = seq.drop(tpd.size)
      for (i <- is) if (i._1) throw ElaboratorException.DimensionLambdaCannotBeImplicit()
      val iss = is.map(_._2)
      val (ll, tt, ctx0) = ctx.inferFlatLevel(tpd)
      ctx = ctx0
      val valueGraph = tt.zipWithIndex.map(kk => Abstract.ClosureGraph.Node(kk._1._2, 0 until kk._2, kk._1._3))
      // FIXME check restrictions is compatible
      def checkRestrictions(sv: Value): Seq[(Abstract.Formula, Abstract.MetaEnclosed)] = {
        // NOW: check extensions
        val (dimCtx, dims) = iss.foldLeft((ctx0, Seq.empty[Long])) { (ctx, n) =>
          val (c, l) = ctx._1.newDimension(n)
          isHit = true
          (c, ctx._2 :+ l.id)
        }
        ctx = dimCtx
        c.restrictions.map(r => {
          val (dv, da) = ctx.checkAndEvalFormula(r.dimension)
          val rctx = ctx.newReifierRestrictionLayer(dv)
          val bd = rctx.check(r.term, sv)
          val res = Abstract.MetaEnclosed(rctx.finishReify(), bd)
          (da, res)
        })
      }
      val es: Abstract.EnclosedSystem = if (is.nonEmpty) {
        selfValue match {
          case Some(sv) =>
            checkRestrictions(sv).toMap
          case None =>
            throw ElaboratorException.CannotInferTypeOfHit()
        }
      } else {
        if (c.restrictions.nonEmpty) throw ElaboratorException.HitContainingExternalDimension()
        else Map.empty
      }
      val closureGraph = Abstract.ClosureGraph(valueGraph, iss.size, es)
      selfValue match {
        case Some(_) =>
          ctx = ctx.newConstructor(c.name, eval(closureGraph))
        case None =>
          ctx = newParametersLayer(None) // here we don't use ctx anymore, because we are not remembering the previous constructors
      }
      (c.name, ll, closureGraph)
    })
    val fl = tps.map(_._3).getOrElse(
      if (fs.isEmpty) throw ElaboratorException.EmptySumMustHaveTypeAnnotation() else fs.map(_._2).max)
    (Value.Universe(fl), Abstract.Sum(tps.flatMap(_._2.map(_._2)), isHit, fs.map(a =>
      Abstract.Constructor(a._1, a._3))))
  }

  def checkConstructApp(sumValue: Value, index: Int, nodes: Value.ClosureGraph, arguments: Seq[(Boolean, Concrete)]): Abstract = {
    val ns = arguments.take(nodes.size)
    val res1 = inferGraphValuesPart(nodes, ns)
    val ds = arguments.drop(nodes.size)
    if (ds.size != nodes.dimSize) throw ElaboratorException.NotFullyAppliedConstructorNotSupportedYet()
    if (ds.exists(_._1)) throw ElaboratorException.DimensionLambdaCannotBeImplicit()
    val res2 = ds.map(a => checkAndEvalFormula(a._2))
    Abstract.Construct(index, res1.map(_._1), res2.map(_._2), if (nodes.dimSize == 0) Map.empty else reifyEnclosedSystem(nodes.reduceAll(res1.map(_._2)).reduce(res2.map(_._1)).restrictions()))
  }

  def checkSumConstructApp(sum: Value.Sum, index: Int, arguments: Seq[(Boolean, Concrete)]) =
    checkConstructApp(sum, index, sum.constructors(index).nodes, arguments)

  private def infer(
                     term: Concrete,
                     noReduceMore: Boolean = false): (Value, Abstract) = {
    debug(s"infer $term")
    def reduceMore(v: Value, abs: Abstract): (Value, Abstract) = {
      if (noReduceMore) {
        (v, abs)
      } else {
        finishOffImplicits(v, abs)
      }
    }


    def inferProjectionApp(left: Concrete, right: Concrete, arguments: Seq[(Boolean, Concrete)]): (Value, Abstract) = {
      val (lt, la) = infer(left)
      val lv = eval(la)
      lazy val ltr = lt.whnf.asInstanceOf[Value.Record]
      def error() = throw ElaboratorException.UnknownProjection(right.toString)
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
          val (a,b) = inferApp(m.projectedType(lv, index), Abstract.Projection(la, index), arguments)
          reduceMore(a, b)
        case _ =>
          lv.whnf match {
            // TODO user defined projections for a type, i.e.
            // TODO [issue 7] implement const_projections syntax
            case r: Value.Record if right == Concrete.Make =>
              (lv, Abstract.Make(inferGraphValuesPart(r.nodes, arguments).map(_._1)))
            case r: Value.Sum if calIndex(t => r.constructors.indexWhere(_.name.by(t))) =>
              (r, checkSumConstructApp(r, index, arguments))
            case _ =>
              error()
          }
      }
    }
    val res = term match {
      case Concrete.Type =>
        (Value.Universe.level1, Abstract.Universe(0))
      case Concrete.Up(a, b) =>
        a match {
          case Concrete.Up(c, d) =>
            // @syntax_creation
            infer(Concrete.Up(c, b + d))
          case Concrete.Type =>
            (Value.Universe.suc(b + 1), Abstract.Universe(if (Value.Universe.TypeInType) 0 else b))
          case Concrete.Reference(ref) =>
            lookupTerm(ref) match {
              case NameLookupResult.Typed(typ, abs) =>
                abs match {
                  case Abstract.Reference(up, _) if up == layers.size - 1 =>
                    reduceMore(typ, abs)
                  //reduceMore(binder.up(b), Abstract.Up(abs, b))
                  case _ => throw ElaboratorException.UpCanOnlyBeUsedOnTopLevelDefinitionOrUniverse()
                }
              case _: NameLookupResult.Construct =>
                throw ElaboratorException.UpCanOnlyBeUsedOnTopLevelDefinitionOrUniverse()
            }
          case _ => throw ElaboratorException.UpCanOnlyBeUsedOnTopLevelDefinitionOrUniverse()
        }
      case Concrete.Reference(name) =>
        // should lookup always return a value? like a open reference?
        lookupTerm(name) match {
          case NameLookupResult.Typed(binder, abs) =>
            reduceMore(binder, abs)
          case NameLookupResult.Construct(self, index, closure) =>
            if (closure.size != 0 || closure.dimSize != 0) {
              throw ElaboratorException.NotFullyAppliedConstructorNotSupportedYet()
            } else {
              (self, Abstract.Construct(index, Seq.empty, Seq.empty, Abstract.EnclosedSystem.empty))
            }
        }
      case Concrete.Hole =>
        throw ElaboratorException.CannotInferMeta()
      case Concrete.True =>
        throw ElaboratorException.TermSortWrong()
      case Concrete.False =>
        throw ElaboratorException.TermSortWrong()
      case _: Concrete.And =>
        throw ElaboratorException.TermSortWrong()
      case _: Concrete.Or =>
        throw ElaboratorException.TermSortWrong()
      case _: Concrete.Neg =>
        throw ElaboratorException.TermSortWrong()
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
      case r: Concrete.Record =>
        checkRecord(None, r)
      case s: Concrete.Sum =>
        checkSum(None, s)
      case Concrete.Transp(tp, direction, base) =>
        val (dv, da) = checkAndEvalFormula(direction)
        val (tv, ta) = checkTypeLine(tp)
        val cl = eval(ta)
        val (ctx, dim) = newDimensionLayer(Name.empty)
        val constant = dv.normalForm.filter(a => semantic.Formula.Assignments.satisfiable(a)).forall(asg => {
          ctx.newSyntaxDirectedRestrictionLayer(asg).unifyTerm(Value.Universe(tv), cl(dim).restrict(asg), cl(semantic.Formula.False).restrict(asg))
        })
        if (!constant) {
          throw ElaboratorException.TranspShouldBeConstantOn()
        }
        val ba = check(base, cl(semantic.Formula.False))
        (cl(semantic.Formula.True), Abstract.Transp(ta, da, ba))
      case Concrete.Comp(tp, base, faces) =>
        val (_, ta) = checkTypeLine(tp)
        val cl = eval(ta)
        val ba = check(base, cl(semantic.Formula.False))
        val rs = checkCompatibleCapAndFaces(faces, cl, eval(ba))
        (cl(semantic.Formula.True), Abstract.Comp(ta, ba, rs))
      case Concrete.Hcomp(base, faces) =>
        val (bt, ba) = infer(base)
        val bv = eval(ba)
        val rs = checkCompatibleCapAndFaces(faces, Value.AbsClosure(bt), bv)
        val btr = reify(bt.bestReifyValue)
        debug(s"infer hcom type $btr", 1)
        (bt, Abstract.Hcomp(btr, ba, rs))
      case Concrete.PathType(typ, left, right) =>
        typ match {
          case Some(tp) =>
            val (tl, ca) = checkTypeLine(tp)
            val tv = eval(ca)
            val la = check(left, tv(semantic.Formula.False))
            val ra = check(right, tv(semantic.Formula.True))
            (Value.Universe(tl), Abstract.PathType(ca, la, ra))
          case None =>
            // FIXME(META) instead of inferring two side, infer one side then check another; or if we have meta with levels... can we just write a max level? it seems not that easy... because you run into the same kind of problems
            val (lt, la) = infer(left)
            val (rt, ra) = infer(right)
            val ttt = if (subTypeOf(lt, rt)) {
              Some(rt)
            } else if (subTypeOf(rt, lt)) {
              Some(lt)
            } else None
            ttt match {
              case Some(t) =>
                val ta = newDimensionLayer(Name.empty)._1.reify(t.bestReifyValue)
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
          // @syntax_creation
          val (ta, va) = inferTelescope(Seq((false, l.name, Concrete.I)), None, l.body)
          (eval(ta), va)
        } else {
          throw ElaboratorException.CannotInferLambda()
        }
      case Concrete.App(lambda, arguments) =>
        @inline def defaultCase(lt: Value, la: Abstract) = {
          val (v1, v2) = inferApp(lt, la, arguments)
          reduceMore(v1, v2) // because inferApp stops when arguments is finished
        }
        lambda match {
          case Concrete.App(l2, a2) =>
            // @syntax_creation
            infer(Concrete.App(l2, a2 ++ arguments))
          case Concrete.Projection(left, right) =>
            inferProjectionApp(left, right, arguments)
          case Concrete.Reference(name) =>
            lookupTerm(name) match {
              case NameLookupResult.Typed(typ, ref) => defaultCase(typ, ref)
              case NameLookupResult.Construct(self, index, closure) =>
                (self, checkConstructApp(self, index, closure, arguments))
            }
          case _ =>
            val (lt, la) = infer(lambda, true)
            defaultCase(lt, la)
        }
      case Concrete.Projection(left, right) =>
        inferProjectionApp(left, right, Seq.empty)
      case Concrete.GlueType(ty, faces) =>
        val (lv, ta) = inferLevel(ty)
        val tv = eval(ta)
        val facesA = faces.map(f => {
          val formula = checkAndEvalFormula(f.dimension)
          val ba = doForValidFormulaOrThrow(formula._1, asgn => {
            val ctx = newSyntaxDirectedRestrictionLayer(asgn).newDimensionLayer(Name.empty)._1 // this is currently a hack!
            // TODO here we checked by same level as ty.
            val bd = ctx.check(f.term, Value.App(BuiltIn.equiv_of, tv).restrict(asgn))
            Abstract.MetaEnclosed(ctx.finishReify(), bd)
          })
          (formula._2, ba)
        }).toMap
        (Value.Universe(lv), Abstract.GlueType(ta, facesA))
      case Concrete.Unglue(m) =>
        val (mt, ma) = infer(m)
        mt.whnf match {
          case Value.GlueType(ty, faces) =>
            (ty, Abstract.Unglue(reify(ty.bestReifyValue), ma, false, reifyEnclosedSystem(faces.view.mapValues(_.bestReifyValue).toMap)))
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

  private def checkAndEvalFormula(r: Concrete): (semantic.Formula, Abstract.Formula) = {
    val a = checkFormula(r)
    (eval(a), a)
  }
  // it always returns formulas with assignments inlined
  private def checkFormula(r: Concrete): Abstract.Formula = {
    r match {
      case Concrete.Reference(name) =>
         lookupDimension(name).ref
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

  private def inferFlatLevel(fs: Concrete.NameType.FlatSeq): (Int, Seq[(Name, Boolean, Abstract.MetaEnclosed)], Self) = {
    var ctx = this
    var l = 0
    // FIXME it used be like this, but I forget what it is for
    // if (fs.map(_._2).toSet.size != fs.size) throw ElaboratorException.AlreadyDeclared()
    val fas = fs.map(n => {
      val (fl, fa) = ctx.inferLevel(n._3)
      l = l max fl
      val ms = ctx.freezeReify()
      val (ctx1, g) = ctx.newParameter(n._2, ctx.eval(fa))
      ctx = ctx1
      (n._2, n._1, Abstract.MetaEnclosed(ms, fa))
    })
    (l, fas, ctx)
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
            val left = clov(semantic.Formula.False)
            val right = clov(semantic.Formula.True)
            (Abstract.PathType(Abstract.AbsClosure(ms, ta), reify(left.bestReifyValue), reify(right.bestReifyValue)), Abstract.PathLambda(cloa))
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
            val btr = reify(bt.bestReifyValue)
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

  private def inferGraphValuesPart(nodes: Value.ClosureGraph, arguments: Seq[(Boolean, Concrete)], accumulator: Seq[(Abstract, Value)] = Seq.empty): Seq[(Abstract, Value)] = {
    val i = accumulator.size
    def implicitCase() = {
      val (mv, ma) = newMeta(nodes(i).independent.typ)
      val ns = nodes.reduce(i, mv)
      inferGraphValuesPart(ns, arguments, accumulator.:+((ma, mv)))
    }
    arguments match {
      case head +: tail => // more arguments
        if (i >= nodes.size) {
          throw ElaboratorException.ConstructorWithMoreArguments()
        } else {
          val imp = nodes(i).implicitt
          if (imp == head._1) { // this is a given argument
            val aa = check(head._2, nodes(i).independent.typ)
            val av = eval(aa)
            val ns = nodes.reduce(i, av)
            inferGraphValuesPart(ns, tail, accumulator.:+((aa, av)))
          } else if (imp) { // this is a implicit argument not given
            implicitCase()
          } else {
            throw ElaboratorException.NotExpectingImplicitArgument()
          }
        }
      case Seq() =>
        if (i == nodes.size) { // no argument and no field, perfect!
          accumulator
        } else {
          if (nodes(i).implicitt) { // more implicits, finish off
            implicitCase()
          } else { // no more implicits, we want to wrap the thing in lambda
            throw ElaboratorException.NotFullyAppliedConstructorNotSupportedYet()
          }
        }
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
                     lambdaNameHints: Seq[Name] = Seq.empty,
                     indState: IndState = IndState.stop
  ): Abstract = {
    debug(s"check $term")
    val (hint, tail) = lambdaNameHints match {
      case head +: tl => (head, tl)
      case _ => (Name.empty, Seq.empty)
    }
    def fallback(): Abstract = {
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
    term match {
      case Concrete.Hole =>
        newMeta(cp)._2
      case Concrete.Let(declarations, bd) =>
        val (ctx, ms, da) = newDefinesLayer().checkDeclarations(declarations, false)
        val ba = ctx.check(bd, cp)
        val ms0 = ctx.freezeReify()
        Abstract.Let(ms ++ ms0, da, ba)
      case _ =>
        cp.whnf match {
          case Value.Function(domain, fimp, codomain) =>
            term match {
              case Concrete.Lambda(n, limp, ensuredPath, body) if fimp == limp =>
                assert(!ensuredPath)
                val (ctx, v) = newParameterLayer(n.nonEmptyOrElse(hint), domain)
                val ba = ctx.check(body, codomain(v), tail, indState.app(v))
                Abstract.Lambda(Abstract.Closure(ctx.finishReify(), ba))
              case Concrete.PatternLambda(limp, cases) if fimp == limp =>
                val res = cases.map(c => {
                  val (ctx, v, pat) = newPatternLayer(c.pattern, domain)
                  val ba = ctx.check(c.body, codomain(v), tail)
                  Abstract.Case(pat, Abstract.MultiClosure(ctx.finishReify(), ba))
                })
                Abstract.PatternLambda(Elaborator.pgen(), reify(domain.bestReifyValue), reify(codomain), res)
              case _ =>
                if (fimp) {
                  val (ctx, v) = newParameterLayer(Name.empty, domain)
                  val ba = ctx.check(term, codomain(v), tail)
                  Abstract.Lambda(Abstract.Closure(ctx.finishReify(), ba))
                } else {
                  fallback()
                }
            }
          case v@Value.Universe(l) =>
            term match {
              case s: Concrete.Sum =>
                val ind = indState.consume(l)
                checkSum(Some((v, ind, l)), s)._2
              case r: Concrete.Record =>
                val ind = indState.consume(l)
                checkRecord(ind.map(_._2), r)._2
              case _ =>
                fallback()
            }
          case Value.GlueType(ty, faces) =>
            term match {
              case Concrete.Glue(base, fs) =>
                val ba = check(base, ty)
                val bv = eval(ba)
                val phi1 = semantic.Formula.phi(faces.keys)
                val ffs = fs.map(a => { val (f1, f2) = checkAndEvalFormula(a.dimension); (f1, f2, a.term) })
                val phi2 =  semantic.Formula.phi(ffs.map(_._1))
                if (phi1 == phi2) {
                  val fas = ffs.map(f => {
                    val body = doForValidFormulaOrThrow(f._1, asgn => {
                      val terms = mutable.Set.empty[Abstract.MetaEnclosed]
                      for (tf <- faces) {
                        tf._1.normalForm.filter(semantic.Formula.Assignments.satisfiable).foreach(asgn2 => {
                          val asg = asgn ++ asgn2
                          if (semantic.Formula.Assignments.satisfiable(asg)) {
                            val ctx = newSyntaxDirectedRestrictionLayer(asg).newDimensionLayer(Name.empty)._1
                            val bd1 = tf._2.restrict(asg)
                            val res = ctx.check(f._3, Value.Projection(bd1, 0))
                            val itemv = eval(res)
                            if (ctx.unifyTerm(ty.restrict(asg), bv.restrict(asg), Value.App(Value.Projection(bd1, 1), itemv))) {
                              terms.add(Abstract.MetaEnclosed(ctx.finishReify(), res))
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
                    (f._2, body)
                  }).toMap
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
                import semantic.Formula._
                val a1 = c1.check(body, t1, tail)
                val ps = Abstract.AbsClosure(c1.finishReify(), a1)
                info("path body:"); print(Abstract.PathLambda(ps))
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
            term match {
              case Concrete.App(Concrete.Make, vs) =>
                Abstract.Make(inferGraphValuesPart(r.nodes, vs).map(_._1))
              case _ =>
                fallback()
            }
          case r: Value.Sum =>
            term match {
              case Concrete.Projection(Concrete.Hole, Concrete.Reference(name)) =>
                r.constructors.indexWhere(_.name.by(name)) match {
                  case -1 => fallback()
                  case a => checkSumConstructApp(r, a, Seq.empty)
                }
              case Concrete.App(Concrete.Projection(Concrete.Hole, Concrete.Reference(name)), as) =>
                r.constructors.indexWhere(_.name.by(name)) match {
                  case -1 => fallback()
                  case a => checkSumConstructApp(r, a, as)
                }
              case _ => fallback()
            }
          case _ => fallback()
        }
    }
  }

  private def newReference(v: Value = null, name: Name = null): Value.Reference =
    if (layers.size == 1) {
      val g = Value.GlobalReference(v)
      g.name = name
      g
    }
    else Value.LocalReference(v)

  def debugNv(whnf: Value): Value = whnf.whnf match {
    case n: Value.Construct if n.ds.isEmpty =>
      Value.Construct(n.name, n.vs.map(debugNv), n.ds, n.ty)
    case a => a
  }

  // should we make sure type annotation is the minimal type?
  // ANS: we don't and we actually cannot
  private def checkDeclaration(
      s: Declaration.Single,
      mis: mutable.ArrayBuffer[CodeInfo[Value.Meta]],
      vis: mutable.ArrayBuffer[DefinitionInfo], topLevel: Boolean): Self = {
    // @syntax_creation
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
    val ret = s match {
      case Declaration.Define(ms, name, ps, t0, v) =>
        // TODO implement with constructor
        //        if (ms.contains(Modifier.WithConstructor)) {
        //        }
        // a inductive type definition
        var inductively: IndState = IndState.stop
        def rememberInductivelyBy(ty: Abstract, self: Value) = {
          inductively = if (ms.contains(Modifier.Inductively)) {
            if (topLevel) {
              new IndState(Elaborator.igen(),ty,  false, self)
            } else {
              throw ElaboratorException.RecursiveTypesMustBeDefinedAtTopLevel()
            }
          } else IndState.stop
          inductively
        }
        val ret = lookupDefined(name) match {
          case Some((index, item)) =>
            if (item.isDefined) {
              throw ElaboratorException.AlreadyDefined()
            }
            info(s"check defined $name")
            if (ps.nonEmpty || t0.nonEmpty) throw ElaboratorException.SeparateDefinitionCannotHaveTypesNow()
            // FIXME it is an example why define layers should also save all code, this way the reify bellow is not necessary
            val va = check(v, item.typ, Seq.empty, rememberInductivelyBy(reify(item.typ), item.ref))
            info("body:"); print(va)
            appendMetas(freeze())
            val ref = newReference(name = name)
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
              info("type:"); print(ta)
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
              val va = ctx.check(wrapBody(v, pps.map(_._1)), tv, lambdaNameHints, rememberInductivelyBy(ta, generic))
              info("body:"); print(va)
              appendMetas(ctx.freeze())
              val ref = newReference(name = name)
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
              info("type:"); print(ta)
              info("body:"); print(va)
              appendMetas(freeze())
              val ref = newReference(eval(va), name = name)
              val (ctx, index, generic) = newDefinition(name, eval(ta), ref)
              fillTo(vis, index); assert(vis(index) == null)
              vis.update(index, DefinitionInfo(Some(CodeInfo(va, ref)), CodeInfo(ta, generic)))
              info(s"inferred $name")
              ctx
          }
        }
        if (!inductively.stop) throw ElaboratorException.InductiveModifierNotApplyable()
        ret
      case Declaration.Declare(ms, name, ps, t) =>
        lookupDefined(name) match {
          case Some(_) =>
            throw ElaboratorException.AlreadyDeclared()
          case None =>
            info(s"declare $name")
            if (ms.exists(_ != Modifier.__Debug)) throw ElaboratorException.ForbiddenModifier()
            val (_, ta) = inferTelescope(NameType.flatten(ps), t)
            info("type:"); print(ta)
            appendMetas(freeze())
            val tv = eval(ta)
            val (ctx, index, generic) = newDeclaration(name, tv)
            fillTo(vis, index); assert(vis(index) == null)
            vis.update(index, DefinitionInfo(None, CodeInfo(ta, generic)))
            info(s"declared $name")
            ctx
        }
    }
    if (s.modifiers.contains(Declaration.Modifier.__Debug)) {
      val a = ret.layers.head.asInstanceOf[Layer.Defines].terms.find(_.name == s.name).get
      val kkk = a.ref0 match {
        case Some(v) =>
          Value.NORMAL_FORM_MODEL = true
          val time  = System.currentTimeMillis()
          def printRes(a: String, j: Value) = {
            println(s"DEBUG used time: ${System.currentTimeMillis() - time}")
            loopBase(j)
            println(s"__DEBUG__ WHNF $a:")
            println(j)
          }
          val k = debugNv(v.value.whnf)
          k match {
            case lambda: Value.PathLambda =>
              val j = debugNv(lambda.body(semantic.Formula.Generic(2131)))
              printRes("LAMBDA", j)
            case _ =>
              printRes("", k)
          }
          Value.NORMAL_FORM_MODEL = false
          val a = 1
        case _ =>
      }
    }
    ret
  }



  private def checkDeclarations(seq0: Seq[Declaration], topLevel: Boolean): (Self, Seq[Abstract], Seq[Abstract]) = {
    // how to handle mutual recursive definitions, calculate strong components
    def flatten(d: Declaration, ps: Seq[NameType]): Seq[Declaration.Single] = d match {
      case d: Declaration.Define =>
        Seq(d.copy(parameters = ps ++ d.parameters))
      case d: Declaration.Declare =>
        Seq(d.copy(parameters = ps ++ d.parameters))
      case Declaration.Parameters(parameters, items) =>
        items.flatMap(a => flatten(a, ps ++ parameters))
    }
    val seq = seq0.flatMap(a => flatten(a, Seq.empty))
    var ctx = this
    val ms = mutable.ArrayBuffer.empty[CodeInfo[Value.Meta]]
    val vs = mutable.ArrayBuffer.empty[DefinitionInfo]
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
      case _ =>
        throw ElaboratorException.UnknownAsType()
    }
  }


  def check(m: Module): Elaborator = Benchmark.TypeChecking {
    checkDeclarations(m.declarations, true)._1
  }


  // debug metthods
  def loopType(a: Value.AbsClosure): Value = loopBase(a(semantic.Formula.Generic(-Random.nextLong(Long.MaxValue / 2))))
  def loopBase(k: Value): Value = {
    k.whnf match {
      case h: Value.Hcomp =>
        h.tp.whnf match {
          case a: Value.Sum =>
            if (a.hit) {
              loopBase(h.base)
            } else {
              loopBase(h.base)
            }
          case a: Value.Function =>
            logicError()
          case a: Value.PathType =>
            logicError()
          case a: Value.Record =>
            logicError()
          case a: Value.GlueType =>
            logicError()
          case _ =>
            loopBase(h.tp)
        }
      case t: Value.Transp =>
        t.tp(semantic.Formula.Generic(-Random.nextLong(Long.MaxValue / 2))).whnf match {
          case _: Value.Sum =>
            loopBase(t.base)
          case a: Value.Function =>
            logicError()
          case a: Value.PathType =>
            logicError()
          case a: Value.Record =>
            logicError()
          case a: Value.GlueType =>
            logicError()
          case a: Value.Universe =>
            logicError()
          case Value.Hcomp(v: Value.Universe, _, _) =>
            logicError()
          case a =>
            loopType(t.tp)
        }
      case t: Value.Glue =>
        assert(!t.faces.exists(_._1.normalFormTrue))
        loopBase(t.m)
      case v: Value.Unglue =>
        loopBase(v.base)
      case a: Value.GlueType =>
        assert(!a.faces.exists(_._1.normalFormTrue))
        k
      case Value.PathType(typ, left, right) =>
        k
      case c: Value.Construct =>
        k
      case Value.Make(values) =>
        k
      case PathLambda(body) =>
        k
      case a: Value.Function =>
        k
      case a: Value.Record =>
        k
      case a: Value.Universe =>
        k
      case a: Value.Lambda =>
        k
      case a: Value.PatternLambda =>
        k
      case Value.PatternRedux(a, b) =>
        b.whnf match {
          case h: Value.Hcomp =>
            h
          case a: Value.Construct =>
            a
          case _ =>
            loopBase(b)
        }
      case Value.Projection(a, b) =>
        loopBase(a)
      case g: Value.Generic =>
        k
      case Value.PathApp(a, _) =>
        loopBase(a)
    }
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



