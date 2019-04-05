package mlang.core.checker

import mlang.core.concrete.{Name, Pattern, Term}
import Context._
import mlang.core
import mlang.core.checker


// the reason we have this is because sometimes values is compond of their smaller ones, make and construct
private trait NeedsValue {
  type V
  def just(byName: => Value): V
  def map(t: V, m: Value => Value): V
  def flatMap(t: Seq[V], m: Seq[Value] => Value): V

  // these are infer, level and check results, they all might return a value depends on if you asked
  case class I(typ: Value, value: V)
  case class L(level: Int, value: V) {
    def assertLeq(l2: Int): V = {
      if (level <= l2) {
        value
      } else {
        throw new Exception("Universe level inconsistent")
      }
    }
  }
}

private object Y extends NeedsValue {
  type V = Value
  override def just(byName: => Value): Value = byName
  override def map(t: Value, m: Value => Value): Value = m(t)
  override def flatMap(t: Seq[Value], m: Seq[Value] => Value) = m(t)
}

private object N extends NeedsValue {
  type V = Unit
  override def just(byName: => Value): Unit = Unit
  override def map(t: Unit, m: Value => Value): Unit = Unit
  override def flatMap(t: Seq[Unit], m: Seq[Value] => Value) = Unit
}




sealed class TypeCheckException extends Exception

object TypeCheckException {
  // name intro
  class AlreadyDeclared() extends TypeCheckException
  class AlreadyDefined() extends TypeCheckException
  class NotDeclared() extends TypeCheckException

  // name resolve
  class NonExistingReference() extends TypeCheckException

  class ExpectingType() extends TypeCheckException
  class NonExistingField() extends TypeCheckException
  class CannotInferLambdaWithoutDomain() extends TypeCheckException
}




class TypeChecker private (protected override val layers: Layers) extends ContextBuilder with Evaluator {
  override type Self = TypeChecker

  override protected implicit def create(a: Layers): Self = new TypeChecker(a)

  def newLayer(): Self = (Map.empty : Layer) +: layers

  def newDeclaration(name: Name, typ: Value) : Self = {
    layers.last.get(name) match {
      case Some(_) => throw new TypeCheckException.AlreadyDeclared()
      case _ => layers.last.updated(name, Binder(generic(), typ)) +: layers.tail
    }
  }

  def newDefinition(name: Name, v: Value) : Self = {
    layers.last.get(name) match {
      case Some(Binder(id, typ, v)) => v match {
        case Some(_) => throw new TypeCheckException.AlreadyDefined()
        case _ => layers.last.updated(name, Binder(id, typ, v)) +: layers.tail
      }
      case _ => throw new TypeCheckException.NotDeclared()
    }
  }

  def newDefinition(name: Name, typ: Value, v: Value): Self = {
    layers.last.get(name) match {
      case Some(_) => throw new TypeCheckException.AlreadyDeclared()
      case _ => layers.last.updated(name, Binder(generic(), typ, Some(v))) +: layers.tail
    }
  }

  def newLayerFromPattern(pattern: Pattern, typ: Value): Self = {
    def rec(l: Layer, p: Pattern, t: Value): Layer = {
      (p, t) match {
        case (Pattern.Atom(id), t) =>
          l.updated(id, Binder(generic(), t))
        case (Pattern.Make(maps), Value.Record(names, initials)) =>
          if (maps.map(_._1).forall(names.contains)) {
            ???
          } else {
            throw new TypeCheckException.NonExistingField()
          }
        case (Pattern.Normalized(names), Value.Record(_, _)) =>
          ???
        case (Pattern.Constructor(name, pattern), Value.Sum(_)) =>
          ???
      }
    }
    create(rec(Map.empty, pattern, typ) +: layers)
  }

  private def infer(term: Term, nv: NeedsValue): nv.I = {
    term match {
      case Term.Reference(name) =>
        // should lookup always return a value? like a open reference?
        lookup(name) match {
          case Some(Binder(_, t, Some(v))) => nv.I(t, nv.just(v))
          case _ => throw new TypeCheckException.NonExistingReference()
        }
      case Term.Cast(v, t) =>
        val Y.L(_, tv) = inferLevel(t, Y)
        val vv = check(v, tv, nv)
        nv.I(tv, vv)
      case Term.Function(domain, pattern, codomain) =>
        val Y.L(dl, dv) = inferLevel(domain, Y)
        val N.L(cl, _) = newLayerFromPattern(pattern, dv).inferLevel(codomain, N)
        val ft = Value.Universe(dl max cl)
        nv.I(ft, nv.just(eval(term))) // LATER evalClosure is enough
      case Term.Record(_, fields) =>
        var ctx = newLayer()
        var l = 0
        for (f <- fields) {
          val Y.L(fl, fv) = ctx.inferLevel(f.ty, Y)
          l = l max fl
          ctx = ctx.newDeclaration(f.name, fv)
        }
        // LATER try compose value for simple case instead
        nv.I(Value.Universe(l), nv.just(eval(term)))
      case Term.Sum(constructors) =>
        // TODO in case of HIT, each time a constructor finished, we need to construct a partial sum and update the value
        // LATER sum can absolutely be reconstructed
        nv.I(Value.Universe(constructors.map(c => inferLevel(c.term, Y).level).max), nv.just(eval(term)))
      case Term.Lambda(d0, cases) =>
        d0 match {
          case None =>
            throw new TypeCheckException.CannotInferLambdaWithoutDomain()
          case Some(domain) =>
            // TODO inferring the type of a lambda, the inferred type might not have the same branches as the lambda itself
            // so we need to minimalise the pattern
            // val Y.L(dl, dv) = inferLevel(domain, Y)
            val _ = cases
            val __ = domain
            ???
        }
      //case Term.Application(Term.Projection(obj, name), argument) =>
        // TODO type directed name resolution on argument
      case Term.Projection(left, right) =>
        // TODO type directed name resolution without argumenet
        // this handles: field projection, sum's case construction, and type directed functions
        // when you only have projection, you cannot resolute on application,
        val Y.I(lt, lv) = infer(left, Y)
        def error() = throw new TypeCheckException.NonExistingField()
        lt match {
          case r: Value.Record =>
            if (r.names.contains(right)) {
              ???
            } else {
              error()
            }
          case _: Value.Universe =>
            lv match {
              case Value.Sum(bs) =>
                bs.get(right) match {
                  case Some(constructor) =>
                    ???
                  case _ => error()
                }
              case _ => error()
            }
        }
      case Term.Application(lambda, argument) =>
        val nv.I(lty, lv) = infer(lambda, nv)
        lty match {
          case Value.Function(domain, codomain) =>
            val av = check(argument, domain, Y)
            nv.I(codomain(av), nv.map(lv, _.application(av)))
          case _ => throw new Exception("Cannot infer Application")
        }
      case Term.Let(declarations, in) =>
        ???
    }
  }

  private def check(term: Term, value: Value, nv: NeedsValue): nv.V = {
    ???
  }



  private def inferLevel(term: Term, nv: NeedsValue): nv.L = {
    val res = infer(term, nv)
    res.typ match {
      case Value.Universe(l) => nv.L(l, res.value)
      case _ => throw new TypeCheckException.ExpectingType()
    }
  }
}
