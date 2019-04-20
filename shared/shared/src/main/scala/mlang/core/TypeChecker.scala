package mlang.core

import mlang.concrete.{Pattern => Patt, _}
import Context._
import mlang.name._
import mlang.utils
import mlang.utils.debug

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
  case class EmptyLambdaParameters() extends TypeCheckException

  // elimination mismatch
  case class UnknownAsType() extends TypeCheckException
  case class UnknownProjection() extends TypeCheckException
  case class UnknownAsFunction() extends TypeCheckException
  case class UnknownAsPathType() extends TypeCheckException

  case class CheckingAgainstNonFunction() extends TypeCheckException

  case class CheckingAgainstNonPathFunction() extends TypeCheckException

  case class CannotInferLambda() extends TypeCheckException
  case class CannotInferReturningTypeWithPatterns() extends TypeCheckException
  case class CannotInferPathLambda() extends TypeCheckException


  case class TypeMismatch() extends TypeCheckException

  case class ForbiddenModifier() extends TypeCheckException

  case class DeclarationWithoutDefinition(name: Name) extends TypeCheckException

  case class ExpectingTermButFoundDimension() extends TypeCheckException

  case class ApplyingToNonDimension() extends TypeCheckException

  case class PathEndPointsNotMatching() extends TypeCheckException
}


object TypeChecker {
  private val gen = new GenericGen.Positive()
  val empty = new TypeChecker(Seq(Layer.Terms(Seq.empty)))
  private val rd = Reduction.No
}

import TypeChecker._

class TypeChecker private (protected override val layers: Layers)
    extends ContextBuilder with BaseEvaluator with PlatformEvaluator with Reifier {
  override type Self = TypeChecker

  override protected implicit def create(a: Layers): Self = new TypeChecker(a)


  private def infer(term: Term): (Value, Abstract) = {
    debug(s"infer $term")
    val res = term match {
      case Term.Universe(i) =>
        (Value.Universe(i + 1), Abstract.Universe(i))
      case Term.Reference(name) =>
        // should lookup always return a value? like a open reference?
        val (Binder(_, _, t, _, _), abs) = lookup(name)
        (t, abs)
      case Term.ConstantDimension(i) =>
        throw ContextException.ConstantSortWrong()
      case Term.Cast(v, t) =>
        val (_, ta) = inferLevel(t)
        val tv = eval(ta, rd)
        (tv, check(v, tv))
      case Term.Function(domain, codomain) =>
        if (domain.isEmpty) throw TypeCheckException.EmptyTelescope()
        val (l, v) = inferTelescope(NameType.flatten(domain), codomain)
        (Value.Universe(l), v)
      case r@Term.Record(fields) =>
        // TODO calculate real record dependencies
        for (f <- fields) {
          if (f.names.isEmpty) throw TypeCheckException.MustBeNamed()
        }
        for (i <- r.names.indices) {
          for (j <- (i + 1) until r.names.size) {
            if (r.names(i) intersect r.names(j)) {
              throw TypeCheckException.FieldsDuplicated()
            }
          }
        }
        val (fl, fs) = newLayer().inferLevel(fields)
        (Value.Universe(fl), Abstract.Record(fl, fs.map(pair => Abstract.RecordNode(pair._1, pair._2))))
      case Term.Sum(constructors) =>
        for (i <- constructors.indices) {
          for (j <- (i + 1) until constructors.size) {
            if (constructors(i).name == constructors(j).name) {
              throw TypeCheckException.TagsDuplicated()
            }
          }
        }
        // TODO in case of HIT, each time a constructor finished, we need to construct a partial sum and update the value
        val fs = constructors.map(c => newLayer().newLayer().inferLevel(c.term))
        val fl = fs.map(_._1).max
        (Value.Universe(fl), Abstract.Sum(fl, fs.map(_._2.map(_._2)).zip(constructors).map(a => Abstract.Constructor(a._2.name, a._1))))
      case Term.Coe(direction, tp, base) =>
        val from = checkDimension(direction.from)
        val to = checkDimension(direction.to)
        val ctx = newDimension(tp._1.getOrElse(Name.empty))._1
        val (_, ta) = ctx.inferLevel(tp._2)
        val tv = eval(Abstract.PathLambda(ta), rd)
        val la = check(base, tv.papp(from._1, rd))
        (tv.papp(to._1, rd), Abstract.Coe(Abstract.DimensionPair(from._2, to._2), ta, la))
      case Term.Hcom(direction, tp, base, restrictions) =>
        val from = checkDimension(direction.from)
        val to = checkDimension(direction.to)
        val (_, ta) = inferLevel(tp)
        val tv = eval(ta, rd)
        val la = check(base, tv)
        // check restrictions is valid
        // check restrictions each over overlapping valid
        // check restrictions with base is valid
        (tv, Abstract.Coe(Abstract.DimensionPair(from._2, to._2), ta, la))
      case Term.PathType(typ, left, right) =>
        typ match {
          case Some(tp) =>
            val ctx = newDimension(tp._1.getOrElse(Name.empty))._1
            val (tl, ta) = ctx.inferLevel(tp._2)
            val tv = eval(Abstract.PathLambda(ta), rd).asInstanceOf[Value.PathLambda]
            val la = check(left, tv.body(Value.Dimension.Constant(false), rd))
            val ra = check(right, tv.body(Value.Dimension.Constant(true), rd))
            (Value.Universe(tl), Abstract.PathType(ta, la, ra))
          case None =>
            throw new IllegalStateException("Not implemented yet")
        }
      case Term.PatternLambda(_) =>
        // TODO inferring the type of a lambda, the inferred type might not have the same branches as the lambda itself
        throw TypeCheckException.CannotInferReturningTypeWithPatterns()
      case Term.Lambda(_, _) =>
        // TODO inferring the type of a lambda, the inferred type might not have the same branches as the lambda itself
        throw TypeCheckException.CannotInferLambda()
      case Term.PathLambda(_, _) =>
        throw TypeCheckException.CannotInferPathLambda()
      case Term.Projection(left, right) =>
        val (lt, la) = infer(left)
        val lv = eval(la, rd)
        def ltr = lt.asInstanceOf[Value.Record]
        def error() = throw TypeCheckException.UnknownProjection()
        lv.whnf match {
          case m: Value.Make if ltr.nodes.exists(_.name.by(right)) =>
            val index = ltr.nodes.indexWhere(_.name.by(right))
            (ltr.projectedType(m.values, index, rd), Abstract.Projection(la, index))
          // TODO user defined projections
          case r: Value.Record if right == Ref.make =>
            (r.makerType, Abstract.RecordMaker(la))
          case r: Value.Sum if r.constructors.exists(_.name == right) =>
            r.constructors.find(_.name == right) match {
              case Some(br) =>
                (br.makerType, Abstract.SumMaker(la, r.constructors.indexWhere(_.name == right)))
              case _ => error()
            }
          case _ => error()
        }
      case Term.Application(lambda, arguments) =>
        if (arguments.isEmpty) throw TypeCheckException.EmptyArguments()
        val (lt, la) = infer(lambda)
        inferApplication(lt, la, arguments)
      case Term.Let(declarations, in) =>
        val (ctx, da, order) = newLayer().checkDeclarations(declarations)
        val (it, ia) = ctx.infer(in)
        (it, Abstract.Let(da, order, ia))
      case Term.PathApplication(let, r) =>
        val (lt, la) = infer(let)
        val dim = checkDimension(r)
        lt.whnf match {
          case Value.PathType(typ, _, _) =>
            (typ(dim._1, rd), Abstract.PathApplication(la, dim._2))
          case _ => throw TypeCheckException.UnknownAsPathType()
        }

    }
    debug(s"infer result ${res._2}")
    res
  }

  private def checkDimension(r: Term): (Value.Dimension, Abstract.Dimension) = {
    r match {
      case Term.Reference(name) =>
        val (v, a) = lookupDimension(name)
        (v.value, a)
      case Term.ConstantDimension(i) =>
        (Value.Dimension.Constant(i), Abstract.Dimension.Constant(i))
      case _ => throw TypeCheckException.ApplyingToNonDimension()
    }
  }

  private def inferTelescope(domain: NameType.FlatSeq, codomain: Term): (Int, Abstract) = {
    domain match {
      case head +: tail =>
        val (dl, da) = inferLevel(head._2)
        var ctx = newLayer()
        head._1 match {
          case Some(n) =>
            ctx = ctx.newAbstraction(n, eval(da, rd))._1
          case _ =>
        }
        val (cl, ca) = ctx.inferTelescope(tail, codomain)
        (dl max cl, Abstract.Function(da, ca))
      case Seq() =>
        val (l, a) = inferLevel(codomain)
        (l, a)
    }
  }

  private def inferApplication(lt: Value, la: Abstract, arguments: Seq[Term]): (Value, Abstract) = {
    arguments match {
      case head +: tail =>
        lt.whnf match {
          case Value.Function(domain, codomain) =>
            val aa = check(head, domain)
            val av = eval(aa, rd)
            val lt1 = codomain(av, rd)
            val la1 = Abstract.Application(la, aa)
            inferApplication(lt1, la1, tail)
            // TODO user defined applications
          case _ => throw TypeCheckException.UnknownAsFunction()
        }
      case Seq() =>
        (lt, la)
    }
  }

  private def hintCodomain(hint: Option[Abstract]):Option[Abstract] = hint match {
    case Some(Abstract.Function(_, b)) => Some(b)
    case _ => None
  }

  private def check(
      term: Term,
      cp: Value,
      lambdaNameHints: Seq[Name.Opt] = Seq.empty,
      lambdaFunctionCodomainHint: Option[Abstract] = None
  ): Abstract = {
    debug(s"check $term")
    val (hint, tail) = lambdaNameHints match {
      case head +: tl => (head, tl)
      case _ => (None, Seq.empty)
    }
    val res = term match {
      case Term.Lambda(n, body) =>
        cp.whnf match {
          case Value.Function(domain, codomain) =>
            val (ctx, v) = newLayer().newAbstraction(n.orElse(hint).getOrElse(Name.empty), domain)
            val ba = ctx.check(body, codomain(v, rd), tail, hintCodomain(lambdaFunctionCodomainHint))
            Abstract.Lambda(ba)
          case _ => throw TypeCheckException.CheckingAgainstNonFunction()
        }
      case Term.PatternLambda(cases) =>
        cp.whnf match {
          case Value.Function(domain, codomain) =>
            Abstract.PatternLambda(TypeChecker.gen(), lambdaFunctionCodomainHint.getOrElse(???), cases.map(c => {
              val (ctx, v, pat) = newLayer().newAbstractions(c.pattern, domain)
              val ba = ctx.check(c.body, codomain(v, rd), tail, hintCodomain(lambdaFunctionCodomainHint))
              Abstract.Case(pat, ba)
            }))
          case _ => throw TypeCheckException.CheckingAgainstNonFunction()
        }
      case Term.PathLambda(name, term) =>
        cp.whnf match {
          case Value.PathType(typ, left, right) =>
            val (c1, dv) = newDimension(name.getOrElse(Name.empty))
            val t1 = typ(dv, rd)
            import Value.Dimension._
            val a1 = c1.check(term, t1)
            val ps = Abstract.PathLambda(a1)
            val pv = eval(ps, rd)
            val leftEq = Conversion.equalTerm(typ(Constant(false), rd), pv.papp(Constant(false), rd), left)
            val rightEq = Conversion.equalTerm(typ(Constant(true), rd), pv.papp(Constant(true), rd), right)
            if (leftEq && rightEq) {
              ps
            } else {
              throw TypeCheckException.PathEndPointsNotMatching()
            }
          case _ => throw TypeCheckException.CheckingAgainstNonPathFunction()
        }
      case _ =>
        val (tt, ta) = infer(term)
        if (Conversion.equalType(tt, cp)) ta
        else throw TypeCheckException.TypeMismatch()
    }
    debug(s"check result $res")
    res
  }

  private def checkDeclaration(s: Declaration, abs: mutable.ArrayBuffer[DefinitionInfo]): Self = {
    def wrapBody(t: Term, n: Int): Term = if (n == 0) t else wrapBody(Term.Lambda(None, t), n - 1)
    s match {
      case Declaration.Define(ms, name, ps, t0, v) =>
        if (ms.contains(Declaration.Modifier.__Debug)) {
          val a = 1
        }
        t0 match {
          case Some(t) =>
            debug(s"check define $name")
            val pps = NameType.flatten(ps)
            val (_, ta) = inferTelescope(pps, t)
            val tv = eval(ta, rd)
            val lambdaNameHints = pps.map(_._1) ++(t match {
              case Term.Function(d, _) =>
                NameType.flatten(d).map(_._1)
              case _ => Seq.empty
            })
            val ctx = newDeclaration(name, tv) // allows recursive definitions
          val va = ctx.check(wrapBody(v, pps.size), tv, lambdaNameHints, hintCodomain(Some(ta)))
            debug(s"declared $name")
            abs.append(DefinitionInfo(name, tv, va, Some(ta)))
            ctx
          case None =>
            if (ps.nonEmpty) throw new Exception("Not implemented")
            val index = headTerms.indexWhere(_.name == name)
            if (index < 0) {
              val (vt, va) = infer(v)
              val ctx = newDeclaration(name, vt)
              debug(s"declared $name")
              abs.append(DefinitionInfo(name, vt, va, None))
              ctx
            } else {
              val b = headTerms(index)
              val va = check(v, b.typ, Seq.empty, hintCodomain(abs(index).typCode))
              debug(s"declared $name")
              abs.update(index, DefinitionInfo(name, b.typ, va, abs(index).typCode))
              this
            }
        }
      case Declaration.Declare(ms, name, ps, t) =>
        debug(s"check declare $name")
        if (ms.nonEmpty) throw TypeCheckException.ForbiddenModifier()
        val (_, ta) = inferTelescope(NameType.flatten(ps), t)
        val tv = eval(ta, rd)
        val ctx = newDeclaration(name, tv)
        debug(s"declared $name")
        abs.append(DefinitionInfo(name, tv, null, Some(ta)))
        ctx
    }

  }

  private def checkDeclarations(seq: Seq[Declaration]): (Self, Seq[Abstract], Seq[Set[Int]]) = {
    // how to handle mutual recursive definitions, calculate strong components
    var ctx = this
    val abs = new mutable.ArrayBuffer[DefinitionInfo]()
    val definitionOrder = new mutable.ArrayBuffer[Set[Int]]()
    for (s <- seq) {
      if (s.modifiers.contains(Declaration.Modifier.Ignored)) {
        ctx.checkDeclaration(s, abs.clone())
      } else {
        ctx = ctx.checkDeclaration(s, abs)
      }
      val toCompile = mutable.ArrayBuffer[Int]()
      for (i <- abs.indices) {
        val t = abs(i)
        if (t.code != null && t.value.isEmpty && t.directDependencies.forall(j => abs(j).code != null)) {
          toCompile.append(i)
        }
      }
      if (toCompile.nonEmpty) {
        val toCal = toCompile.map(i => i -> abs(i).directDependencies.filter(a => toCompile.contains(a))).toMap
        val ccc = utils.graphs.tarjanCcc(toCal).toSeq.sortWith((l, r) => {
          l.exists(ll => r.exists(rr => abs(ll).directDependencies.contains(rr)))
        }).reverse
        for (c <- ccc) {
          assert(c.nonEmpty)
          definitionOrder.append(c)
          if (c.size == 1 && !abs(c.head).directDependencies.contains(c.head)) {
            val g = abs(c.head)
            val v = ctx.eval(g.code, rd)
            g.value = Some(v)
            ctx = ctx.newDefinitionChecked(c.head, g.name, v)
            debug(s"defined ${g.name}")
          } else {
            for (i <- c) {
              abs(i).code.markRecursive(0, c)
            }
            val vs = ctx.evalMutualRecursive(c.map(i => (i, (abs(i).code, abs(i).typ))).toMap, rd)
            for (v <- vs) {
              val ab = abs(v._1)
              ab.value = Some(v._2)
              val name = ab.name
              ctx = ctx.newDefinitionChecked(v._1, name, v._2)
              debug(s"defined recursively $name")
            }
          }
        }
      }
    }
    assert(abs.size == ctx.headTerms.size)
    abs.foreach(f => {
      if (f.code == null) {
        throw TypeCheckException.DeclarationWithoutDefinition(f.name)
      }
    })
    (ctx, abs.map(a => a.code), definitionOrder)
  }


  private def inferLevel(terms: Seq[NameType]): (Int, Seq[(Name, Abstract)]) = {
    var ctx = this
    var l = 0
    val fas = terms.flatMap(f => {
      val fs = if (f.names.isEmpty) Seq(Name.empty) else f.names
      fs.map(n => {
        val (fl, fa) = ctx.inferLevel(f.ty)
        l = l max fl
        ctx = ctx.newAbstraction(n, eval(fa, rd))._1
        (n, fa)
      })
    })
    (l, fas)
  }

  private def inferLevel(term: Term): (Int, Abstract) = {
    val (tt, ta) = infer(term)
    tt.whnf match {
      case Value.Universe(l) => (l, ta)
      // TODO user defined type coercion
      case _ => throw TypeCheckException.UnknownAsType()
    }
  }

  def check(m: Module): TypeChecker = checkDeclarations(m.declarations)._1
}

private case class DefinitionInfo(
    name: Name,
    typ: Value,
    code: Abstract,
    typCode: Option[Abstract],
    var value: Option[Value] = None,
   ) {
   lazy val directDependencies: Set[Int] = code.dependencies(0)
}


