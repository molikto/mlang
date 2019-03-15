package mlang.core


import mlang.syntax._
import mlang.utils._
import Context._


/**

helpers

*/

// the reason we have this is because sometimes values is compond of their smaller ones, make and construct
private trait NeedsValue {
  type V
  def bool: Boolean
  def just(byName: => Value): V
  def map(t: V, m: Value => Value): V

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
  override def bool = true
  override def just(byName: => Value): Value = byName
  override def map(t: Value, m: Value => Value): Value = m(t)
}

private object N extends NeedsValue {
  type V = Unit
  override def bool = false
  override def just(byName: => Value): Unit = Unit
  override def map(t: Unit, m: Value => Value): Unit = Unit
}
private def (c: Context) and[T](init: given Context => T): T = init given c

private def (c: (Context, Value)) and[T](init: given (Context, Value) => T): T = init given (c._1, c._2)

private def result given (c: Value): Value = c

import Context.LookupMethods._
import Context.Builders._




/**

main

*/



private def inferApplication(argument: Term, pi: Value.Pi, nv: NeedsValue, lv: nv.V) given Context: (Value, nv.I) = {
  val av = check(argument, pi.domain, Y)
  // argument type, and infered result
  (av, nv.I(
    pi.codomain(av, Reduction.Default), 
    nv.map(lv, lv => lv.application(eval(argument), Reduction.Default))
  ))
}


private def infer(term: Term, nv: NeedsValue) given Context: nv.I = {
  term match {
    case Term.Reference(name) =>
      // should lookup always return a value? like a open reference?
      lookupValue(name) match {
        case Some(t) => nv.I(t.typ, nv.just(t.value))
        case None => throw new Exception("Cannot find reference")
      }
    case Term.Ascription(body, typ) =>
      val Y.L(lv, bd) = inferLevel(typ, Y)
      nv.I(bd, check(body, bd, nv))
    case Term.Application(lambda, argument) =>
      val nv.I(lty, lv) = infer(lambda, nv)
      lty match {
        case pi: Value.Pi => inferApplication(argument, pi, nv, lv)._2
        case _ => throw new Exception("Cannot infer Application")
      }
    case Term.Projection(term, name) =>
      val Y.I(lty, ev) = infer(term, Y)
      lty match {
        case Value.Record(map) =>
          var cur = map
          var ret: Value = null
          while (cur.initials.nonEmpty && ret == null) {
            if (cur.initials.contains(name)) {
              ret = cur.initials(name)
            }
            cur = cur(cur.initials.map(pair => (pair._1, ev.projection(pair._1, Reduction.Default))))
          }
          if (ret == null) throw new Exception("projection on non-existing names")
          nv.I(ret, nv.just(ev.projection(name, Reduction.Default)))
        case _ => throw new Exception("Cannot infer Projection")
      }
    case Term.Pi(name, domain, codomain) =>
      val Y.L(ld, d) = inferLevel(domain, Y)
      val N.L(lcd, cd) = newAbstraction(name, d).and { inferLevel(codomain, N) }
      val rty = Value.Universe(ld max lcd)
      nv.I(rty, nv.just(eval(term)))
    case Term.Inductive(parameters, typ, constructors) =>
      ???
    case Term.Record(fields) =>
      if (!fields.map(_.name).allDistinct) {
        throw new Exception("Record defined with duplicated field names")
      } else {
        // LATER allow out of order definitions?
        val level = fields.foldLeft((newDeclarations(), 0)) { (pair, field) =>
          val (ctx, level) = pair
          ctx.and {
            val Y.L(lv, v) = inferLevel(field.typ, Y)
            (newTypeDeclaration(field.name, v), level max lv)
          }
        }._2
        nv.I(Value.Universe(level), nv.just(eval(term)))
      }
    case Term.Universe(level) =>
      nv.I(Value.Universe(level + 1), nv.just(Value.Universe(level)))
    case Term.Make(fields) =>
    // a special case of inferable constructor, if all items of make is inferable, then it is inferable
      ???
    case _ =>  // TODO infer lambdas? lambda, case lambda, construct
      throw new Exception("Cannot infer type")
  }
}

private def check(term: Term, typ: Value, nv: NeedsValue) given (ctx: Context): nv.V = {
  def justEval() = nv.just(eval(term))
  (term, typ) match {
    case (Term.Lambda(name, body), Value.Pi(domain, codomain)) =>
      newAbstraction(name, domain).and { check(body, codomain(result, Reduction.Default), N) }
      justEval()
    case (Term.CaseLambda(cases), Value.Pi(domain, codomain)) =>
      domain match {
        case sum@Value.Sum(cs) =>
          if (sum.names.eqUnordered(cases.map(_.name))) {
            throw new Exception("Pattern matching is not covering or contains duplicates")
          } else {
            for (cons <- cs) {
              val c = cases.find(_.name == cons.name).get
              if (!c.fields.allDistinct) {
                throw new Exception("Constructor argument names is not different")
              } else {
                def upAll(ns: Seq[Unicode], tt: Value) given (c: Context): (Context, Seq[Value]) = {
                  (ns, tt) match {
                    case ((n +: tail), Value.Pi(ty, tl)) =>
                      newAbstraction(ns.head, ty).and {
                        val res = upAll(tail, tl(result, Reduction.Default))
                        (res._1, result +: res._2)
                      }
                    case (Nil, Value.Pi(_, _)) =>
                      throw new Exception("Named parameters in case lambda telescope is shorter")
                    case (Nil, _) =>
                      (c, Seq.empty[Value])
                    case _ =>
                      throw new Exception("Named parameters in case lambda telescope is longer")
                  }
                }
                val (cx, vs) = upAll(c.fields, cons.pi)
                cx.and {
                  check(c.body, codomain(Value.Construct(cons.name, vs), Reduction.Default), N)
                }
              }
            }
          }
        case _ => throw new Exception("Pattern matching on non-sum type")
      }
      justEval()
    case (Term.Make(fields), Value.Record(avg)) =>
      ???
    case (Term.Construct(name, args), Value.Sum(ks)) =>
      if (!ks.contains(name)) {
        throw new Exception("Wrong construct")
      } else {
        val pi: Value = ks.find(_.name == name).get.pi
        val (vs, res) = args.foldLeft((Seq.empty[Value], pi)) { (pair, term) =>
          pair match {
            case (vs, pi: Value.Pi) =>
              val (av, N.I(ty, _)) = inferApplication(term, pi, N, Unit)
              (vs :+ av, ty)
            case _ => throw new Exception("Constructor has more arguments")
          }
        }
        res match {
          case _: Value.Pi => throw new Exception("Constructor has less arguments")
          case _ => nv.just(Value.Construct(name, vs))
        }
      }
    case (tm, ty) => 
       val nv.I(ty0, v) = infer(tm, nv)
       if (convertible(ty0, ty)) {
         v
       } else {
         throw new Exception("Type is not converable")
       }
  }
}


private def inferLevel(term: Term, nv: NeedsValue) given Context: nv.L = {
  val res = infer(term, nv)
  res.typ match {
    case Value.Universe(l) => nv.L(l, res.value)
    case _ => throw new Exception("Nt a type")
  }
}

def (c: Context) typecheck(term: Term): Unit = {
  infer(term, N) given c
}