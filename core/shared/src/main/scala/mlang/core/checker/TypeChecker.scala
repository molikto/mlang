package mlang.core.checker

import mlang.core.concrete._
import Context._
import mlang.core
import mlang.core.checker
import mlang.core.concrete.Term.NameType

import scala.collection.mutable
import scala.language.implicitConversions




sealed class TypeCheckException extends Exception

object TypeCheckException {
  // name intro wrong
  class AlreadyDeclared() extends TypeCheckException
  class AlreadyDefined() extends TypeCheckException
  class NotDeclared() extends TypeCheckException

  // name resolve
  class NonExistingReference() extends TypeCheckException

  // elimination mismatch
  class UnknownAsType() extends TypeCheckException
  class UnknownProjection() extends TypeCheckException
  class UnknownAsFunction() extends TypeCheckException

  // pattern mismatch
  class MakePatternWrongSize() extends TypeCheckException
  class MakePatternIsNotRecordType() extends TypeCheckException
  class ConstructPatternUnknownName() extends TypeCheckException
  class ConstructPatternWrongSize() extends TypeCheckException
  class ConstructPatternNotSumType() extends TypeCheckException

  // not enough type information
  class CannotInferLambdaWithoutDomain() extends TypeCheckException

  class TypeMismatch() extends TypeCheckException
}




class TypeChecker private (protected override val layers: Layers) extends ContextBuilder with Conversion with Evaluator {
  override type Self = TypeChecker

  override protected implicit def create(a: Layers): Self = new TypeChecker(a)

  def newLayer(): Self = (Seq.empty : Layer) +: layers

  def newDeclaration(name: Name, typ: Value) : Self = {
    layers.head.find(_.name == name) match {
      case Some(_) => throw new TypeCheckException.AlreadyDeclared()
      case _ => (layers.head :+ Binder(generic(), name, typ)) +: layers.tail
    }
  }

  def newDefinitionChecked(name: Name, v: Value) : Self = {
    layers.head.find(_.name == name) match {
      case Some(Binder(id, _, typ, tv)) => tv match {
        case Some(_) => throw new TypeCheckException.AlreadyDefined()
        case _ => layers.head.updated(layers.head.indexWhere(_.name == name), Binder(id, name, typ, Some(v))) +: layers.tail
      }
      case _ => throw new TypeCheckException.NotDeclared()
    }
  }

  def newDefinition(name: Name, typ: Value, v: Value): Self = {
    layers.head.find(_.name == name) match {
      case Some(_) => throw new TypeCheckException.AlreadyDeclared()
      case _ => (layers.head :+ Binder(generic(), name, typ, Some(v))) +: layers.tail
    }
  }

  def newAbstraction(name: Name, typ: Value) : (Self, Value) = {
    layers.head.find(_.name == name) match {
      case Some(_) => throw new TypeCheckException.AlreadyDeclared()
      case _ =>
        val g = generic()
        val v = Value.OpenReference(g, name)
        ((layers.head :+ Binder(g, name, typ, Some(v))) +: layers.tail, v)
    }
  }

  def compile(pattern: Pattern): Abstract.Pattern = {
    def rec(p: Pattern): Abstract.Pattern = {
      p match {
        case Pattern.Atom(_) =>
          Abstract.Pattern.Atom
        case Pattern.Make(maps) =>
          Abstract.Pattern.Make(maps.map(compile))
        case Pattern.Constructor(name, maps) =>
          Abstract.Pattern.Constructor(name, maps.map(compile))
      }
    }
    rec(pattern)
  }


  def newAbstractions(pattern: Pattern, typ: Value): (Self, Value) = {
    def rec(l: Self, p: Pattern, t: Value): (Self, Value) = {
      p match {
        case Pattern.Atom(id0) =>
          l.newAbstraction(id0, t)
        case Pattern.Make(maps) =>
          typ match {
            case r@Value.Record(nodes) =>
              if (maps.size == nodes.size) {
                var ll = l
                var vs = Map.empty[NameRef, Value]
                for ((m, n) <- maps.zip(nodes)) {
                  val it = r.projectedType(vs, n.name)
                  val (ll0, tv) = rec(l, m, it)
                  ll = ll0
                  vs = vs.updated(n.name, tv)
                }
                (ll, Value.Make(vs))
              } else {
                throw new TypeCheckException.MakePatternWrongSize()
              }
            case _ => throw new TypeCheckException.MakePatternIsNotRecordType()
          }
        case Pattern.Constructor(name, maps) =>
          typ match {
            case Value.Sum(cs) =>
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
            case _ => throw new TypeCheckException.ConstructPatternNotSumType()
          }
      }
    }
    rec(this, pattern, typ)
  }


  private def infer(term: Term): (Value, Abstract) = {
    term match {
      case Term.Reference(name) =>
        // should lookup always return a value? like a open reference?
        lookup(name) match {
          case Some((Binder(_, _, t, _), abs)) => (t, abs)
          case _ => throw new TypeCheckException.NonExistingReference()
        }
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
        (Value.Universe(fl), Abstract.Record(fs.zip(fields).map(pair => Abstract.RecordNode(pair._2.name, pair._1))))
      case Term.Sum(constructors) =>
        // TODO in case of HIT, each time a constructor finished, we need to construct a partial sum and update the value
        val fs = constructors.map(c => newLayer().inferLevel(c.term))
        val fl = fs.map(_._1).max
        (Value.Universe(fl), Abstract.Sum(fs.zip(constructors).map(a => Abstract.Constructor(a._2.name, a._1._2))))
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
            (ltr.projectedType(m.values, right), Abstract.Projection(la, right))
          // TODO user defined projections
          case r: Value.Record if right == NameRef.make =>
            (r.makerType, Abstract.RecordMaker(la))
          case r: Value.Sum if r.constructors.exists(_.name == right) =>
            r.constructors.find(_.name == right) match {
              case Some(br) =>
                (br.makerType, Abstract.SumMaker(la, right))
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
            (codomain(av), Abstract.Application(la, aa))
          case _ => throw new TypeCheckException.UnknownAsFunction()
        }
      case Term.Let(declarations, in) =>
        val (ctx, da) = newLayer().checkDeclarations(declarations)
        val (it, ia) = ctx.infer(in)
        (it, Abstract.Let(da, ia))
    }
  }


  private def check(term: Term, cp: Value): Abstract = {
    (term, cp) match {
      case (Term.Lambda(name, body), Value.Function(domain, codomain)) =>
        val (ctx, v) = newLayer().newAbstraction(name, domain)
        Abstract.Lambda(ctx.check(body, codomain(v)))
      case (Term.PatternLambda(cases), Value.Function(domain, codomain)) =>
        Abstract.PatternLambda(cases.map(c => {
          val (ctx, v) = newLayer().newAbstractions(c.pattern, domain)
          val ba = ctx.check(c.body, codomain(v))
          Abstract.Case(compile(c.pattern), ba)
        }))
      case _ =>
        val (tt, ta) = infer(term)
        if (equalType(tt, cp)) ta
        else throw new TypeCheckException.TypeMismatch()
    }
  }


  private def checkDeclarations(seq: Seq[Declaration]): (Self, Seq[Abstract]) = {
    var ctx = this
    val abs = new mutable.ArrayBuffer[Abstract]()
    seq.map(s => {
      s match {
        case Declaration.Define(name, v, t0) =>
          t0 match {
            case Some(t) =>
              val (_, ta) = inferLevel(t)
              val tv = eval(ta)
              val va = check(v, tv)
              ctx = ctx.newDefinition(name, tv, eval(va))
              abs.append(va)
            case None =>
              val index = layers.head.indexWhere(_.name == name)
              if (index < 0) {
                val (vt, va) = infer(v)
                ctx = ctx.newDefinition(name, vt, eval(va))
                abs.append(va)
              } else {
                val b = layers.head(index)
                val va = check(v, b.typ)
                ctx = ctx.newDefinitionChecked(name, eval(va))
                abs.updated(index, va)
              }
          }
        case Declaration.Declare(name, t) =>
          val (_, ta) = inferLevel(t)
          ctx = ctx.newDeclaration(name, eval(ta))
          abs.append(null)
      }
    })
    (ctx, abs)
  }


  private def inferLevel(terms: Seq[NameType]): (Int, Seq[Abstract]) = {
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
      case _ => throw new TypeCheckException.UnknownAsType()
    }
  }

  def checkModule(m: Module): Unit = newLayer().checkDeclarations(m.declarations)


  def eval(term: Abstract): Value = platformEval(term)
}
