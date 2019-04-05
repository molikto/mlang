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
  override def bool = true
  override def just(byName: => Value): Value = byName
  override def map(t: Value, m: Value => Value): Value = m(t)
  override def flatMap(t: Seq[Value], m: Seq[Value] => Value) = m(t)
}

private object N extends NeedsValue {
  type V = Unit
  override def bool = false
  override def just(byName: => Value): Unit = Unit
  override def map(t: Unit, m: Value => Value): Unit = Unit
  override def flatMap(t: Seq[Unit], m: Seq[Value] => Value) = Unit
}
private def (c: Context) and[T](init: given Context => T): T = init given c

private def (c: (Context, Value)) and[T](init: given (Context, Value) => T): T = init given (c._1, c._2)

private def result given (c: Value): Value = c

import Context.LookupMethods._
import Context.Builders._




/**

main

*/



private def inferApplication(argument: Term, pi: Value.Pi, nv: NeedsValue, lv: nv.V) given Context: nv.I = {
  val av = check(argument, pi.domain, Y)
  // argument type, and infered result
  nv.I(
    pi.codomain(av, Reduction.Default), 
    nv.map(lv, lv => lv.application(eval(argument), Reduction.Default))
  )
}

private def inferAvg(fields: Seq[Term.Parameter]) given Context: Int = {
  fields.foldLeft((newDeclarations(), 0)) { (pair, field) =>
    val (ctx, level) = pair
    ctx.and {
      val Y.L(lv, v) = inferLevel(field.term, Y)
      (newTypeDeclaration(field.name, v)._1, level max lv)
    }
  }._2
}


private def buildAvgContext[T, V](tele: Value.AVG[T, V], name: T => Unicode) given Context: (Map[T, Value], Context) = {
    def rec(collect: Map[T, Value], tele: Value.AVG[T, V]) given (c: Context): (Map[T, Value], Context) = {
    tele match {
      case Value.AVG.Cons(domain, map) =>
        var ctx: Context = c
        val vv = domain.transform((key, typ) => {
          val (cc, v) = newTypeDeclaration(name(key), typ) given ctx
          ctx = cc
          v : Value
        })
        rec(collect ++ vv, map(vv, Reduction.Default)) given ctx
      case Value.AVG.Terminal(_) =>
        (collect, c)
    }
  }
  newDeclarations().and {
    rec(Map.empty, tele)
  }
}

private def checkToAvg[T, V](tele: Value.AVG[T, V], name: T => Unicode, vs: T => Term) given Context: Map[T, Value] = {
  def rec(collect: Map[T, Value], tele: Value.AVG[T, V]) given (c: Context): Map[T, Value] = {
    tele match {
      case Value.AVG.Cons(domain, map) =>
        val vv: Map[T, Value] = domain.transform((key, value) => check(vs(key), value, Y) : Value)
        var ctx: Context = c
        domain.foreach(d => ctx = newDeclaration(name(d._1), vv(d._1), d._2) given ctx)
        rec(vv ++ collect, map(vv, Reduction.Default)) given ctx
      case Value.AVG.Terminal(_) =>
        collect
    }
  }
  newDeclarations().and {
    rec(Map.empty, tele)
  }
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
        case pi: Value.Pi => inferApplication(argument, pi, nv, lv)
        case _ => throw new Exception("Cannot infer Application")
      }
    case Term.Projection(term, name) =>
      val Y.I(lty, ev) = infer(term, Y)
      lty match {
        case Value.Record(map) =>
          var cur = map
          nv.I(
            map.project(name, Reduction.Default, t => ev.projection(t, Reduction.Default)),
            nv.just(ev.projection(name, Reduction.Default))
          )
        case _ => throw new Exception("Cannot infer Projection")
      }
    case Term.Pi(name, domain, codomain) =>
      val Y.L(ld, d) = inferLevel(domain, Y)
      val N.L(lcd, cd) = newAbstraction(name, d).and { inferLevel(codomain, N) }
      val rty = Value.Universe(ld max lcd)
      nv.I(rty, nv.just(eval(term)))
    case Term.Inductive(parameters, constructors) =>
      ???
    case r@Term.Record(fields) =>
      if (!fields.map(_.name).allDistinct) {
        throw new Exception("Record defined with duplicated field names")
      } else {
        r.avg match {
          case Some(avg) => 
            val l = inferAvg(avg.flatMap(_.toSeq).map(a => Term.Parameter(a, fields.find(_.name == a).get.term)))
            nv.I(Value.Universe(l), nv.just(eval(term)))
          case None =>
            throw new Exception("Record fields contains cycles")
        }
      }
    case Term.Universe(level) =>
      nv.I(Value.Universe(level + 1), nv.just(Value.Universe(level)))
    case Term.Make(fields, dependent) =>
    val fs = fields.map(a => a.term match {
      case Term.Ascription(body, typ) => (a.name, body, typ)
      case _ => throw new Exception("Cannot infer type of field without a annotation")
    })
    if (!fs.map(_._1).allDistinct) {
      throw new Exception("Make expression contains duplicated names")
    } else if (dependent) {
      // make a fake record type and check against
      val ty = Term.Record(fs.map(a => Term.Definition(a._1, a._3)))
      val Y.I(_, rty) = infer(ty, Y)
      nv.I(rty, check(Term.Make(fs.map(a => Term.Definition(a._1, a._2)), dependent), rty, nv))
    } else {
      ???
    }
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
        case Value.Sum(cs) =>
          if (cs.map(_.name).eqUnordered(cases.map(_.name))) {
            throw new Exception("Pattern matching is not covering or contains duplicates")
          } else {
            for (cons <- cs) {
              val c = cases.find(_.name == cons.name).get
              if (!c.fields.allDistinct) {
                throw new Exception("Constructor argument names is not different")
              } else {
                val (frees, ctx1) = buildAvgContext(cons.tele, i => c.fields.getOrElse(i, throw new Exception("Argument size is smaller")))
                if (frees.size < c.fields.size) {
                  throw new Exception("Constructor argument size is bigger than expected")
                } else {
                  ctx1.and {
                    check(c.body, codomain(Value.Construct(cons.name, frees.toSeqByKey), Reduction.Default), N)
                  }
                }
              }
            }
          }
        case _ => throw new Exception("Pattern matching on non-sum type")
      }
      justEval()
    case (Term.Make(fields, dependent), Value.Record(avg)) =>
      if (!fields.map(_.name).allDistinct) {
        throw new Exception("Make names not distinct")
      } else {
        // case not allowed:
        // t1 -> 
        // 
        val vs = checkToAvg(avg, i => i, n => fields.find(_.name == n) match {
          case Some(a) => a.term
          case None => throw new Exception("Make lacking field")
        })
        if (vs.size != fields.size) {
          throw new Exception("Make has more fields")
        } else {
          nv.just(Value.Make(vs))
        }
      }
    case (Term.Construct(name, args), Value.Sum(ks)) =>
      ks.find(_.name == name) match {
        case None => throw new Exception("Wrong construct")
        case Some(Value.Constructor(_, tele)) =>
          // there is no mutual reference in custructor, so it is ok to give it just toString
          val vs = checkToAvg(tele, i => Unicode(i), i => if (i >= args.length) throw new Exception("Constructor has less arguments") else args(i))
          if (vs.size != args.size) {
            throw new Exception("Constructor has more arguments")
          } else {
            nv.just(Value.Construct(name, vs.toSeqByKey))
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