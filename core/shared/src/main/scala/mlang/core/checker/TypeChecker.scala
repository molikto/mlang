package mlang.core.checker

import mlang.core.concrete._
import Context._
import mlang.core.utils.debug

import scala.collection.mutable
import scala.language.implicitConversions




sealed trait TypeCheckException extends CoreException

object TypeCheckException {

  // elimination mismatch
  class UnknownAsType() extends TypeCheckException
  class UnknownProjection() extends TypeCheckException
  class UnknownAsFunction() extends TypeCheckException

  // pattern mismatch

  // not enough type information
  class CannotInferLambdaWithoutDomain() extends TypeCheckException

  class TypeMismatch() extends TypeCheckException

  class CannotInferReturningTypeWithPatterns() extends TypeCheckException
}




class TypeChecker private (protected override val layers: Layers) extends ContextBuilder with Conversion with BaseEvaluator with PlatformEvaluator {
  override type Self = TypeChecker

  override protected implicit def create(a: Layers): Self = new TypeChecker(a)

  private def infer(term: Term): (Value, Abstract) = {
    debug(s"infer $term")
    val res = term match {
      case Term.Universe(i) =>
        (Value.Universe(i + 1), Abstract.Universe(i))
      case Term.Reference(name) =>
        // should lookup always return a value? like a open reference?
        val (Binder(_, _, t, _), abs) = lookup(name)
        (t, abs)
      case Term.Cast(v, t) =>
        val (_, ta) = inferLevel(t)
        val tv = eval(ta)
        (tv, check(v, tv))
      case Term.Function(domain, name, codomain) =>
        val (dl, da) = inferLevel(domain)
        val (cl, ca) = newLayer().newAbstraction(name, eval(da))._1.inferLevel(codomain)
        val ft = Value.Universe(dl max cl)
        (ft, Abstract.Function(da, ca))
      case Term.Record(fields) =>
        val (fl, fs) = newLayer().inferLevel(fields)
        (Value.Universe(fl), Abstract.Record(fl, fs.zip(fields).map(pair => Abstract.RecordNode(pair._2.name, pair._1))))
      case Term.Sum(constructors) =>
        // TODO in case of HIT, each time a constructor finished, we need to construct a partial sum and update the value
        val fs = constructors.map(c => newLayer().inferLevel(c.term))
        val fl = fs.map(_._1).max
        (Value.Universe(fl), Abstract.Sum(fl, fs.zip(constructors).map(a => Abstract.Constructor(a._2.name, a._1._2))))
      case Term.Lambda(_, _) =>
        // TODO inferring the type of a lambda, the inferred type might not have the same branches as the lambda itself
        throw new TypeCheckException.CannotInferLambdaWithoutDomain()
      case Term.PatternLambda(_) =>
        // TODO inferring the type of a lambda, the inferred type might not have the same branches as the lambda itself
        throw new TypeCheckException.CannotInferLambdaWithoutDomain()
      case Term.Projection(left, right) =>
        val (lt, la) = infer(left)
        val lv = eval(la)
        def ltr = lt.asInstanceOf[Value.Record]
        def error() = throw new TypeCheckException.UnknownProjection()
        lv match {
          case m: Value.Make if ltr.nodes.exists(_.name == right) =>
            val index = ltr.nodes.indexWhere(_.name == right)
            (ltr.projectedType(m.values, index), Abstract.Projection(la, index))
          // TODO user defined projections
          case r: Value.Record if right == NameRef.make =>
            (r.makerType, Abstract.RecordMaker(la))
          case r: Value.Sum if r.constructors.exists(_.name == right) =>
            r.constructors.find(_.name == right) match {
              case Some(br) =>
                (br.makerType, Abstract.SumMaker(la, r.constructors.indexWhere(_.name == right)))
              case _ => error()
            }
          case _ => error()
        }
      case Term.Application(lambda, argument) =>
        val (lt, la) = infer(lambda)
        lt match {
          case Value.Function(domain, codomain) =>
            val aa = check(argument, domain)
            val av = eval(aa)
            (codomain(Seq(av)), Abstract.Application(la, aa))
          case _ => throw new TypeCheckException.UnknownAsFunction()
        }
      case Term.Let(declarations, in) =>
        val (ctx, da) = newLayer().checkDeclarations(declarations)
        val (it, ia) = ctx.infer(in)
        (it, Abstract.Let(da, ia))
    }
    debug(s"infer result ${res._2}")
    res
  }


  private def check(term: Term, cp: Value): Abstract = {
    debug(s"check $term")
    val res = (term, cp) match {
      case (Term.Lambda(name, body), Value.Function(domain, codomain)) =>
        val (ctx, v) = newLayer().newAbstraction(name, domain)
        Abstract.Lambda(ctx.check(body, codomain(Seq(v))))
      case (Term.PatternLambda(cases), Value.Function(domain, codomain)) =>
        Abstract.PatternLambda(codomain, cases.map(c => {
          val (ctx, v) = newLayer().newAbstractions(c.pattern, domain)
          val ba = ctx.check(c.body, codomain(Seq(v)))
          Abstract.Case(compile(c.pattern), ba)
        }))
      case _ =>
        val (tt, ta) = infer(term)
        if (equalType(Int.MaxValue, tt, cp)) ta
        else throw new TypeCheckException.TypeMismatch()
    }
    debug(s"check result ${res}")
    res
  }

  private def checkDeclaration(s: Declaration, abs: mutable.ArrayBuffer[Abstract]): Self = {
    s match {
      case Declaration.Define(name, tele, t0, v0) =>
        debug(s"check define $name")
        t0 match {
          case Some(t) =>
            val (_, ta) = inferLevel(t)
            val tv = eval(ta)
            val va = check(v, tv)
            val ctx = newDefinition(name, tv, eval(va))
            debug(s"defined $name")
            ctx
          case None =>
            v0 match {
              case Left(v) =>
                val index = layers.head.indexWhere(_.name == name)
                if (index < 0) {
                  val (vt, va) = infer(v)
                  val ctx = newDefinition(name, vt, eval(va))
                  debug(s"defined $name")
                  abs.append(va)
                  ctx
                } else {
                  val b = layers.head(index)
                  val va = check(v, b.typ)
                  val ctx = newDefinitionChecked(name, eval(va))
                  debug(s"defined body $name")
                  abs.updated(index, va)
                  ctx
                }
              case _ => throw new TypeCheckException.CannotInferReturningTypeWithPatterns()
            }
        }
      case Declaration.Declare(name, tele, t) =>
        debug(s"check declare $name")
        val (_, ta) = inferLevel(t)
        val ctx = newDeclaration(name, eval(ta))
        debug(s"declared $name")
        abs.append(null)
        ctx
    }

  }

  private def checkDeclarations(seq: Seq[Declaration]): (Self, Seq[Abstract]) = {
    // TODO recursive defines
    var ctx = this
    val abs = new mutable.ArrayBuffer[Abstract]()
    for (s <- seq) {
      ctx = ctx.checkDeclaration(s, abs)
    }
    (ctx, abs)
  }


  private def inferLevel(terms: Seq[NamesType]): (Int, Seq[Abstract]) = {
    var ctx = this
    var l = 0
    val fas = terms.map(f => {
      val (fl, fa) = ctx.inferLevel(f.ty)
      l = l max fl
      ctx = ctx.newAbstraction(f.name, eval(fa))._1
      fa
    })
    (l, fas)
  }

  private def inferLevel(term: Term): (Int, Abstract) = {
    val (tt, ta) = infer(term)
    tt match {
      case Value.Universe(l) => (l, ta)
      // TODO user defined type coercion
      case _ => throw new TypeCheckException.UnknownAsType()
    }
  }

  def checkModule(m: Module): Unit = newLayer().checkDeclarations(m.declarations)
}

object TypeChecker {
  val empty = new TypeChecker(Seq.empty)
}
