package mlang.core.checker

import mlang.core.concrete.{Pattern => Patt, _}
import Context._
import mlang.core.name._
import mlang.core.utils.debug

import scala.collection.mutable
import scala.language.implicitConversions




sealed trait TypeCheckException extends CoreException

object TypeCheckException {


  // names
  class NamesDuplicated() extends TypeCheckException
  class MustBeNamed() extends TypeCheckException
  class EmptyTelescope() extends TypeCheckException
  class EmptyArguments() extends TypeCheckException
  class EmptyLambdaParameters() extends TypeCheckException

  // elimination mismatch
  class UnknownAsType() extends TypeCheckException
  class UnknownProjection() extends TypeCheckException
  class UnknownAsFunction() extends TypeCheckException

  class CheckingAgainstNonFunction() extends TypeCheckException

  // pattern mismatch

  // not enough type information
  class CannotInferLambdaWithoutDomain() extends TypeCheckException

  class TypeMismatch() extends TypeCheckException

  class CannotInferReturningTypeWithPatterns() extends TypeCheckException

  class ForbiddenModifier() extends TypeCheckException
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
      case Term.Function(domain, codomain) =>
        if (domain.isEmpty) throw new TypeCheckException.EmptyTelescope()
        val (l, v) = inferFunction(NameType.flatten(domain), codomain)
        (Value.Universe(l), v)
      case r@Term.Record(fields) =>
        // TODO calculate real record dependencies
        for (f <- fields) {
          if (f.names.isEmpty) throw new TypeCheckException.MustBeNamed()
        }
        for (i <- r.names.indices) {
          for (j <- (i + 1) until r.names.size) {
            if (r.names(i)intersect (r.names(j))) {
              throw new TypeCheckException.NamesDuplicated()
            }
          }
        }
        val (fl, fs) = newLayer().inferLevel(fields)
        (Value.Universe(fl), Abstract.Record(fl, fs.map(pair => Abstract.RecordNode(pair._1, pair._2))))
      case Term.Sum(constructors) =>
        for (i <- constructors.indices) {
          for (j <- (i + 1) until constructors.size) {
            if (constructors(i).name == constructors(j).name) {
              throw new TypeCheckException.NamesDuplicated()
            }
          }
        }
        // TODO in case of HIT, each time a constructor finished, we need to construct a partial sum and update the value
        val fs = constructors.map(c => newLayer().inferLevel(c.term))
        val fl = fs.map(_._1).max
        (Value.Universe(fl), Abstract.Sum(fl, fs.map(_._2.map(_._2)).zip(constructors).map(a => Abstract.Constructor(a._2.name, a._1))))
      case Term.PatternLambda(_) =>
        // TODO inferring the type of a lambda, the inferred type might not have the same branches as the lambda itself
        throw new TypeCheckException.CannotInferLambdaWithoutDomain()
      case Term.Lambda(_, _) =>
        // TODO inferring the type of a lambda, the inferred type might not have the same branches as the lambda itself
        throw new TypeCheckException.CannotInferLambdaWithoutDomain()
      case Term.Projection(left, right) =>
        val (lt, la) = infer(left)
        val lv = eval(la)
        def ltr = lt.asInstanceOf[Value.Record]
        def error() = throw new TypeCheckException.UnknownProjection()
        lv match {
          case m: Value.Make if ltr.nodes.exists(_.name.by(right)) =>
            val index = ltr.nodes.indexWhere(_.name.by(right))
            (ltr.projectedType(m.values, index), Abstract.Projection(la, index))
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
        if (arguments.size == 0) throw new TypeCheckException.EmptyArguments()
        val (lt, la) = infer(lambda)
        inferApplication(lt, la, arguments)
      case Term.Let(declarations, in) =>
        val (ctx, da) = newLayer().checkDeclarations(declarations)
        val (it, ia) = ctx.infer(in)
        (it, Abstract.Let(da, ia))
    }
    debug(s"infer result ${res._2}")
    res
  }

  private def inferFunction(domain: NameType.FlatSeq, codomain: Term): (Int, Abstract) = {
    domain match {
      case head +: tail =>
        val (dl, da) = inferLevel(head._2)
        var ctx = newLayer()
        head._1 match {
          case Some(n) =>
            ctx = ctx.newAbstraction(n, eval(da))._1
          case _ =>
        }
        val (cl, ca) = ctx.inferFunction(tail, codomain)
        (dl max cl, Abstract.Function(da, ca))
      case Seq() =>
        inferLevel(codomain)
    }
  }

  private def inferApplication(lt: Value, la: Abstract, arguments: Seq[Term]): (Value, Abstract) = {
    arguments match {
      case head +: tail =>
        lt match {
          case Value.Function(domain, codomain) =>
            val aa = check(head, domain)
            val av = eval(aa)
            val lt1 = codomain(Seq(av))
            val la1 = Abstract.Application(la, aa)
            inferApplication(lt1, la1, tail)
            // TODO user defined applications
          case _ => throw new TypeCheckException.UnknownAsFunction()
        }
      case Seq() =>
        (lt, la)
    }
  }

  private def checkFallback(term: Term, cp: Value): Abstract = {
    val (tt, ta) = infer(term)
    if (equalType(Int.MaxValue, tt, cp)) ta
    else throw new TypeCheckException.TypeMismatch()
  }

  private def checkLambda(names: Seq[Name], body: Term, cp: Value): Abstract = {
    names match {
      case head +: tail =>
        cp match {
          case Value.Function(domain, codomain) =>
            val (ctx, v) = newLayer().newAbstraction(head, domain)
            Abstract.Lambda(ctx.checkLambda(tail, body, codomain(Seq(v))))
          case _ => throw new TypeCheckException.CheckingAgainstNonFunction()
        }
      case Seq() =>
        check(body, cp)
    }
  }

  private def check(term: Term, cp: Value, lambdaNameHints: Option[Seq[Name.Opt]] = None): Abstract = {
    debug(s"check $term")
    val (hint, tail) = lambdaNameHints match {
      case Some(head +: tail) => (head, Some(tail))
      case _ => (None, None)
    }
    val res = term match {
      case Term.Lambda(n, body) =>
        cp match {
          case Value.Function(domain, codomain) =>
            val (ctx, v) = newLayer().newAbstraction(n.orElse(hint).getOrElse(Name.empty), domain)
            val ba = ctx.check(body, codomain(Seq(v)), tail)
            Abstract.Lambda(ba)
          case _ => throw new TypeCheckException.CheckingAgainstNonFunction()
        }
      case Term.PatternLambda(cases) =>
        cp match {
          case Value.Function(domain, codomain) =>
            Abstract.PatternLambda(codomain, cases.map(c => {
              val (ctx, v, pat) = newLayer().newAbstractions(c.pattern, domain)
              val ba = ctx.check(c.body, codomain(Seq(v)), tail)
              Abstract.Case(pat, ba)
            }))
          case _ => throw new TypeCheckException.CheckingAgainstNonFunction()
        }
      case _ =>
        checkFallback(term, cp)
    }
    debug(s"check result $res")
    res
  }

  private def checkDeclaration(s: Declaration, abs: mutable.ArrayBuffer[Abstract]): Self = {
    s match {
      case Declaration.DefineInferred(name, ms, v) =>
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
      case Declaration.Define(name, ms, t, v) =>
        debug(s"check define $name")
        val (_, ta) = inferLevel(t)
        val tv = eval(ta)
        val lambdaNameHints = t match {
          case Term.Function(d, _) =>
            Some(NameType.flatten(d).map(_._1))
          case _ => None
        }
        var ctx = newDeclaration(name, tv) // allows recursive definitions
        val va = ctx.check(v, tv, lambdaNameHints)
        ctx = ctx.newDefinitionChecked(name, eval(va))
        debug(s"defined $name")
        ctx
      case Declaration.Declare(name, ms, t) =>
        debug(s"check declare $name")
        if (ms.nonEmpty) throw new TypeCheckException.ForbiddenModifier()
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
      if (s.modifiers.contains(Declaration.Modifier.Ignored)) {
        ctx.checkDeclaration(s, mutable.ArrayBuffer[Abstract]())
      } else {
        ctx = ctx.checkDeclaration(s, abs)
      }
    }
    (ctx, abs)
  }


  private def inferLevel(terms: Seq[NameType]): (Int, Seq[(Name, Abstract)]) = {
    var ctx = this
    var l = 0
    val fas = terms.flatMap(f => {
      f.names.map(n => {
        val (fl, fa) = ctx.inferLevel(f.ty)
        l = l max fl
        ctx = ctx.newAbstraction(n, eval(fa))._1
        (n, fa)
      })
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

  def check(m: Module): TypeChecker = checkDeclarations(m.declarations)._1
}

object TypeChecker {
  val empty = new TypeChecker(Seq(Seq.empty))
}
