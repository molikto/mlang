package mlang.core.checker

import mlang.core.concrete._
import Context._
import mlang.core.concrete.Term.NameType

import scala.collection.mutable
import scala.language.implicitConversions


private trait NeedsValue {
  type V
  def just(byName: => Value): V
  def map(t: V, m: Value => Value): V
  def flatMap(t: Seq[V], m: Seq[Value] => Value): V

  case class I(typ: Value, value: V)
  case class L(level: Int, value: V)
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
  override def flatMap(t: Seq[Unit], m: Seq[Value] => Value): Unit = Unit
}




sealed class TypeCheckException extends Exception

object TypeCheckException {
  // name intro
  class AlreadyDeclared() extends TypeCheckException
  class AlreadyDefined() extends TypeCheckException
  class NotDeclared() extends TypeCheckException

  // name resolve
  class NonExistingReference() extends TypeCheckException


  // elimination mismatch
  class UnknownAsType() extends TypeCheckException
  class UnknownProjection() extends TypeCheckException
  class UnknownAsFunction() extends TypeCheckException

  class MakePatternWrongSize() extends TypeCheckException
  class ConstructPatternUnknownName() extends TypeCheckException
  class ConstructPatternWrongSize() extends TypeCheckException


  // not enough type information
  class CannotInferLambdaWithoutDomain() extends TypeCheckException

  class TypeMismatch() extends TypeCheckException
}




class TypeChecker private (protected override val layers: Layers) extends ContextBuilder with Evaluator  with Conversion {
  override type Self = TypeChecker

  override protected implicit def create(a: Layers): Self = new TypeChecker(a)

  def newLayer(): Self = (Map.empty : Layer) +: layers

  def newDeclaration(name: Name, typ: Value) : Self = {
    layers.last.get(name) match {
      case Some(_) => throw new TypeCheckException.AlreadyDeclared()
      case _ => layers.last.updated(name, Binder(generic(), typ)) +: layers.tail
    }
  }

  def newDefinitionChecked(name: Name, v: Value) : Self = {
    layers.last.get(name) match {
      case Some(Binder(id, typ, tv)) => tv match {
        case Some(_) => throw new TypeCheckException.AlreadyDefined()
        case _ => layers.last.updated(name, Binder(id, typ, Some(v))) +: layers.tail
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

  def newAbstraction(name: Name, typ: Value) : (Self, Value) = {
    layers.last.get(name) match {
      case Some(_) => throw new TypeCheckException.AlreadyDeclared()
      case _ =>
        val g = generic()
        val v = Value.OpenReference(g, name)
        (layers.last.updated(name, Binder(g, typ, Some(v))) +: layers.tail, v)
    }
  }

  implicit def discardAbstraction(t: (Self, Value)): Self = t._1

  def newAbstractionLayerFromPattern(pattern: Pattern, typ: Value): (Self, Value) = {
    def rec(l: Layer, p: Pattern, t: Value): (Layer, Value) = {
      (p, t) match {
        case (Pattern.Atom(id0), _) =>
          val g = generic()
          val o = Value.OpenReference(g, id0)
          (l.updated(id0, Binder(g, t, Some(o))), o)
        case (Pattern.Make(maps), r@Value.Record(nodes)) =>
          if (maps.size == nodes.size) {
            var ll = l
            val vs = new mutable.ArrayBuffer[Value]()
            for ((m, n) <- maps.zip(nodes)) {
              val it = r.projectedType(vs, n.name)
              val (ll0, tv) = rec(l, m, it)
              ll = ll0
              vs.append(tv)
            }
            (ll, Value.Make(vs))
          } else {
            throw new TypeCheckException.MakePatternWrongSize()
          }
        case (Pattern.Constructor(name, maps), Value.Sum(cs)) =>
          cs.find(_.name == name) match {
            case Some(c) =>
              if (c.nodes.size == maps.size) {
                var ll = l
                val vs = new mutable.ArrayBuffer[Value]()
                for ((m, n) <- maps.zip(c.nodes)) {
                  val it = n(vs)
                  val (ll0, tv) = rec(l, m, it)
                  ll = ll0
                  vs.append(tv)
                }
                (ll, Value.Construct(name, vs))
              } else {
                throw new TypeCheckException.ConstructPatternWrongSize()
              }
            case _ =>
              throw new TypeCheckException.ConstructPatternUnknownName()
          }
      }
    }
    val res = rec(Map.empty, pattern, typ)
    (create(res._1 +: layers), res._2)
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
      case Term.Function(domain, name, codomain) =>
        val Y.L(dl, dv) = inferLevel(domain, Y)
        val N.L(cl, _) = newLayer().newAbstraction(name, dv).inferLevel(codomain, N)
        val ft = Value.Universe(dl max cl)
        nv.I(ft, nv.just(eval(term))) // LATER evalClosure is enough
      case Term.Record(fields) =>
        nv.I(Value.Universe(newLayer().inferLevel(fields)), nv.just(eval(term)))
      case Term.Sum(constructors) =>
        // TODO in case of HIT, each time a constructor finished, we need to construct a partial sum and update the value
        // LATER sum can absolutely be reconstructed
        nv.I(Value.Universe(constructors.map(c => newLayer().inferLevel(c.term)).max), nv.just(eval(term)))
      case Term.Lambda(d0, cases) =>
        // TODO inferring the type of a lambda, the inferred type might not have the same branches as the lambda itself
        throw new TypeCheckException.CannotInferLambdaWithoutDomain()
      case Term.Projection(left, right) =>
        val Y.I(lt, lv) = infer(left, Y)
        def ltr = lt.asInstanceOf[Value.Record]
        lv match {
          case m: Value.Make if ltr.nodes.exists(_.name == right) =>
            nv.I(ltr.projectedType(m.values, right), nv.just(m.project(right)))
          // TODO user defined projections
          case r: Value.Record if right == NameRef.make =>
            nv.I(r.makeType, nv.just(r.make))
          case r: Value.Sum if r.constructors.exists(_.name == right) =>
            val br = r.constructors(right)
            nv.I(br.makeType, nv.just(br.make))
          case _ =>
            throw new TypeCheckException.UnknownProjection()
        }
      case Term.Application(lambda, argument) =>
        val nv.I(lty, lv) = infer(lambda, nv)
        lty match {
          case Value.Function(domain, codomain) =>
            val av = check(argument, domain, Y)
            nv.I(codomain(av), nv.map(lv, _.app(av)))
          case _ => throw new TypeCheckException.UnknownAsFunction()
        }
      case Term.Let(declarations, in) =>
        newLayer().checkDeclarations(declarations).infer(in, nv)
    }
  }


  private def check(term: Term, cp: Value, nv: NeedsValue): nv.V = {
    (term, cp) match {
      case (Term.Lambda(name, body), Value.Function(domain, codomain)) =>
        val (ctx, v) = newLayer().newAbstraction(name, domain)
        ctx.check(body, codomain(v), nv)
      case (Term.PatternLambda(cases), Value.Function(domain, codomain)) =>
        for (c <- cases) {
          val (ctx, v) = newAbstractionLayerFromPattern(c.pattern, domain)
          ctx.check(c.body, codomain(v), nv)
        }
        nv.just(eval(term))
      case (t, v) =>
        val nv.I(tt, ty) = infer(term, nv)
        if (convertableType(tt, cp)) ty
        else throw new TypeCheckException.TypeMismatch()
    }
  }


  private def checkDeclarations(seq: Seq[Declaration]): Self = {
    var ctx = this
    for (s <- seq) {
      s match {
        case Declaration.Define(name, v, t0) =>
          t0 match {
            case Some(t) =>
              val Y.L(_, tv) = inferLevel(t, Y)
              val vv = check(v, tv, Y)
              ctx = ctx.newDefinition(name, tv, vv)
            case None =>
              ctx.lookup(name) match {
                case Some(b: Binder) =>
                  val Y.I(vt, vv) = check(v, b.typ, Y)
                  ctx = ctx.newDefinitionChecked(name, vt)
                case None =>
                  val Y.I(vt, vv) = infer(v, Y)
                  ctx = ctx.newDefinition(name, vt, vv)
              }
          }
        case Declaration.Declare(name, t) =>
          val Y.L(_, tv) = inferLevel(t, Y)
          ctx = ctx.newDeclaration(name, tv)
      }
    }
    ctx
  }


  private def inferLevel(terms: Seq[NameType]): Int = {
    var ctx = this
    var l = 0
    for (f <- terms) {
      val Y.L(fl, fv) = ctx.inferLevel(f.ty, Y)
      l = l max fl
      ctx = ctx.newAbstraction(f.name, fv)
    }
    l
  }

  private def inferLevel(term: Term, nv: NeedsValue): nv.L = {
    val res = infer(term, nv)
    res.typ match {
      case Value.Universe(l) => nv.L(l, res.value)
      case _ => throw new TypeCheckException.UnknownAsType()
    }
  }

  def checkModule(m: Module): Unit = newLayer().checkDeclarations(m.declarations)
}
