package mlang.compiler

import mlang.compiler.GenLong.Negative.{dgen, gen}
import mlang.compiler.Value._
import mlang.utils.{Benchmark, Name, debug}

import scala.collection.mutable
import scala.util.{Failure, Success, Try}

private case class Assumption(left: Long, right: Long, domain: Value, codomain: Value.Closure)

private case class BreakException() extends Exception()

object SolvableMetaForm {
  def unapply(a: Value): Option[(Value.Meta, Value.MetaState.Open, Seq[Value])] = {
    def rec(a: Value): Option[(Value.Meta, Value.MetaState.Open, Seq[Value])] = {
      a match {
        case App(l, as) => rec(l).map(pair => (pair._1, pair._2, pair._3 :+ as))
        case m@Meta(o: MetaState.Open) => Some((m, o, Seq.empty))
        case _ => None
      }
    }
    rec(a)
  }
}


trait ValueConversion {
  protected def unifyTerm(typ: Value, t1: Value, t2: Value): Boolean = {
    Benchmark.Unify {
      recTerm(typ, t1, t2)
    }
  }

  protected def subTypeOf(tm1: Value, tm2: Value): Boolean = {
    Benchmark.Unify {
      recType(tm1, tm2, mode = 1)
    }
  }

  def unifyFailedFalse(): Boolean = {
    false
  }

  def unifyFailed[T](): Option[T] = {
    None
  }

  private implicit def optToBool[T](opt: Option[T]): Boolean = opt.isDefined


  private def recClosureGraph(selfValue: Value, n1: ClosureGraph, n2: ClosureGraph, mode: Int = 0): Boolean = {
    if (n1.size == n2.size && n1.dimSize == n2.dimSize) {
      var gs = Seq.empty[Value.Generic]
      var g1 = n1
      var g2 = n2
      var eq = true
      var i = 0
      while (i < n1.size && eq) {
        val g1i = g1(i)
        val g2i = g2(i)
        eq = g1i.implicitt == g2i.implicitt
        if (eq) {
          val t1 = g1(i).independent.typ
          val t2 = g2(i).independent.typ
          eq = recType(t1, t2, mode)
          val g = Generic(gen(), choose(t1, t2, mode))
          gs = gs :+ g
          g1 = g1.reduce(i, g)
          g2 = g2.reduce(i, g)
          i += 1
        }
      }
      if (eq) {
        if (n1.dimSize == 0) {
          true
        } else {
          val ds = (0 until n1.dimSize).map(_ => Value.Formula.Generic(dgen()))
          g1 = g1.reduce(ds)
          g2 = g2.reduce(ds)
          val phiEq = g1.phi().normalForm == g2.phi().normalForm
          if (phiEq) {
            recValueSystem(selfValue, g1.restrictions(), g2.restrictions())
          } else {
            unifyFailedFalse()
          }
        }
      } else {
        unifyFailedFalse()
      }
    } else {
      unifyFailedFalse()
    }
  }



  private def recConstructor(t: Value, c1: Constructor, c2: Constructor, mode: Int = 0): Boolean = {
    c1.name == c2.name && recClosureGraph(t, c1.nodes, c2.nodes, mode)
  }



  private def recTypeClosure(t: Value, c1: Closure, c2: Closure, mode: Int = 0): Option[Value] = {
    val c = Generic(gen(), t)
    val tt = c1(c)
    if (recType(tt, c2(c), mode)) {
      Some(tt)
    } else {
      unifyFailed()
    }
  }


  private def recTypeAbsClosure(t1: AbsClosure, t2: AbsClosure, mode: Int = 0): Boolean = {
    val c = Formula.Generic(dgen())
    recType(t1(c), t2(c), mode)
  }


  def recInd(dd1: Inductively, dd2: Inductively): Boolean = dd1.id == dd2.id && {
     // if id is equal, then type is equal
    assert(dd1.ps.size == dd2.ps.size)
    dd1.ps.zip(dd2.ps).foldLeft(Some(dd1.typ): Option[Value]) { (tp, ds) =>
      tp match {
        case Some(v) =>
          val func = v.whnf.asInstanceOf[Value.Function]
          val d = func.domain
          if (recTerm(d, ds._1, ds._2)) {
            Some(func.codomain(ds._1))
          } else {
            unifyFailed()
          }
        case _ => tp
      }
    }
  }

  @inline def maybeNominal(id1: Option[Inductively], id2: Option[Inductively], el: => Boolean): Boolean = {
    (id1, id2) match {
      case (None, None) =>
        // structural
        el
      case (Some(dd1), Some(dd2)) => recInd(dd1, dd2) // nominal
      case _ => unifyFailedFalse()
    }

  }

  // FIXME is this handling of subtyping sound?
  def choose(d1: Value, d2: Value, mode: Int): Value = if (mode >= 0) d1 else d2

  def forCompatibleAssignments[T](t: System[T], r1: System[T], r2: System[T])(handle: (Formula.Assignments, T, T, T) => Boolean): Boolean = {
    val pht = Formula.phi(t.keys)
    val ph1 = Formula.phi(r1.keys)
    val ph2 = Formula.phi(r2.keys)
    assert(pht == ph1 && ph2 == pht)
    try {
      for (ft <- t) {
        val ast = ft._1.normalForm
        for (at <- ast) {
          for (f1 <- r1) {
            for (f2 <- r2) {
              val as1 = f1._1.normalForm
              val as2 = f2._1.normalForm
              for (a1 <- as1) {
                for (a2 <- as2) {
                  val a = at ++ a1 ++ a2
                  if (Formula.Assignments.satisfiable(a)) {
                    // FIXME before we create a new layer, but now we don't, because we simply don't allow restriction on meta, think again if this is proper
                    // newSyntaxDirectedRestrictionLayer(a)
                    if (handle(a, ft._2, f1._2, f2._2)) {
                    } else {
                      throw BreakException()
                    }
                  }
                }
              }
            }
          }
        }
      }
      true
    } catch {
      case _: BreakException => unifyFailedFalse()
    }
  }

  def forCompatibleAssignments[T](r1: System[T], r2: System[T])(handle: (Formula.Assignments, T, T) => Boolean): Boolean = {
    val ph1 = Formula.phi(r1.keys)
    val ph2 = Formula.phi(r2.keys)
    try {
      if (ph1 == ph2) {
        for (f1 <- r1) {
          for (f2 <- r2) {
            val as1 = f1._1.normalForm
            val as2 = f2._1.normalForm
            for (a1 <- as1) {
              for (a2 <- as2) {
                val a = a1 ++ a2
                if (Formula.Assignments.satisfiable(a)) {
                  // FIXME before we create a new layer, but now we don't, because we simply don't allow restriction on meta, think again if this is proper
                  // newSyntaxDirectedRestrictionLayer(a)
                  if (handle(a, f1._2, f2._2)) {
                  } else {
                    throw BreakException()
                  }
                }
              }
            }
          }
        }
        true
      } else {
        unifyFailedFalse()
      }
    } catch {
      case _: BreakException => unifyFailedFalse()
    }
  }


  /**
    * mode = 1 left =<subtype< right
    * mode = 0 left == right
    * mode =-1 right =< left
    */
  private def recType(tm1: Value, tm2: Value, mode: Int = 0): Boolean = {
    if (tm1.eq(tm2)) {
      true
    } else {
      (tm1.whnf, tm2.whnf) match {
        case (Function(d1, i1, c1), Function(d2, i2, c2)) =>
          i1 == i2 && recType(d1, d2, -mode) && recTypeClosure(choose(d1, d2, -mode), c1, c2, mode)
        case (Universe(l1), Universe(l2)) =>
          mode match {
            case -1 => l2 <= l1
            case 0 => l1 == l2
            case 1 => l1 <= l2
          }
        case (Record(id1, i1, n1), Record(id2, i2, n2)) =>
          // need to check level because of up operator
          maybeNominal(id1, id2, i1 == i2 && recClosureGraph(null, n1, n2, mode))
        case (s1@Sum(id1, c1), s2@Sum(id2, c2)) =>
          maybeNominal(id1, id2, c1.size == c2.size && c1.zip(c2).forall(p => recConstructor(choose(s1, s2, mode), p._1, p._2, mode)))
        case (PathType(t1, l1, r1), PathType(t2, l2, r2)) =>
          recTypeAbsClosure(t1, t2, mode) &&
            recTerm(t1(Formula.False), l1, l2) &&
            recTerm(t1(Formula.True), r1, r2)
        case (GlueType(a1, r1), GlueType(a2, r2)) =>
          // FIXME is this treatment of glue + subtype correct?
          recType(a1, a2, mode) && recGlueFaces(choose(a1, a2, mode), r1, r2)
        case (t1, t2) =>
          recNeutral(t1, t2).map(_.whnf match {
            case Universe(_) => true
            case _ => logicError()
          })
      }
    }
  }




  /**
    *
    *
    * term part
    *
    */



  // FIXME this is potentially non-terminating now, if the domain/codomain changes each time, this can happens for indexed types I think
  private val patternAssumptions = mutable.ArrayBuffer[Assumption]()

  private def sameTypePatternLambdaWithAssumptions(domain: Value, l1: PatternLambda, l2: PatternLambda): Boolean = {
    if (l1.id == l2.id) {
      true
    } else {
      if (patternAssumptions.exists(a => a.left == l1.id && a.right == l2.id && recType(a.domain, domain) && recTypeClosure(a.domain, a.codomain, l1.typ))) {
        true
      } else {
        patternAssumptions.append(Assumption(l1.id, l2.id, domain, l1.typ))
        recCases(domain, l1.typ, l1.cases, l2.cases)
      }
    }
  }

  private def recAbsClosure(typ: Value, t1: AbsClosure, t2: AbsClosure): Boolean = {
    val c = Formula.Generic(dgen())
    recTerm(typ, t1(c), t2(c))
  }


  protected def trySolve(m: Meta, vs: Seq[Value], t20: Value): Option[Value]

  private def recNeutral(tmm1: Value, tmm2: Value): Option[Value] = {
    (tmm1.whnf, tmm2.whnf) match {
      case (Generic(i1, v1), Generic(i2, v2)) =>
        if (i1 == i2) {
          if (v1.eq(v2)) {
            Some(v1)
          } else {
            logicError()
          }
        } else {
          unifyFailed()
        }
      case (App(l1, a1), App(l2, a2)) =>
        recNeutral(l1, l2).flatMap(_.whnf match {
          case Function(d, _, c) =>
            if (recTerm(d, a1, a2)) {
              Some(c(a1))
            } else {
              unifyFailed()
            }
          case _ => logicError()
        })
      case (Projection(m1, f1), Projection(m2, f2)) =>
        recNeutral(m1, m2).flatMap(_.whnf match {
          case r: Record if f1 == f2 => Some(r.projectedType(m1, f2))
          case _ => logicError()
        })
      case (PatternRedux(l1, s1), PatternRedux(l2, s2)) =>
        if (recType(l1.domain, l2.domain)) {
          val n = l1.domain
          if (recTerm(l1.domain, s1, s2)) {
            if (recTypeClosure(n, l1.typ, l2.typ) && sameTypePatternLambdaWithAssumptions(n, l1, l2)) {
              Some(l1.typ(s1))
            } else unifyFailed()
          } else unifyFailed()
        } else unifyFailed()
      case (PathApp(l1, d1), PathApp(l2, d2)) =>
        if (d1.normalForm == d2.normalForm) {
          recNeutral(l1, l2).map(_.whnf match {
            case PathType(typ, _, _) =>
              typ(d1)
            case _ => logicError()
          })
        } else {
          unifyFailed()
        }
      case (Hcomp(t1, b1, r1), Hcomp(t2, b2, r2)) =>
        if (debug.enabled) { // here because we know they are of same type
          if (!recType(t1, t2)) {
            logicError()
          }
        }
        val res = forCompatibleAssignments(r1, r2) { (a, b1, b2) =>
          recAbsClosure(t1.restrict(a), b1.restrict(a), b2.restrict(a))
        }
        if (res) Some(t1) else unifyFailed()
      case (Transp(t1, d1, b1), Transp(t2, d2, b2)) =>
        if (d1.normalForm == d2.normalForm && recTypeAbsClosure(t1, t2) && recTerm(t1(Value.Formula.False), b1, b2)) {
          Some(t1(Value.Formula.True))
        } else {
          unifyFailed()
        }
      case (Unglue(t1, b1, f1), Unglue(t2, b2, f2)) =>
        if (debug.enabled) { // here because we know they are of same type
          if (!recType(t1, t2)) {
            logicError()
          }
          if (!recGlueFaces(t1, f1, f2)) {
            logicError()
          }
        }
        recNeutral(b1, b2).map(_ => t1)
      // FIXME solve meta headed?
      //      case (SolvableMetaForm(m1, o1, gs1), SolvableMetaForm(m2, o2, gs2)) if o1.id == o2.id =>
      //        if (gs1.size == gs2.size) {
      //          gs1.zip(gs2).foldLeft(Some(o1.typ)) {
      //          }
      //        } else {
      //          None
      //        }
      case (SolvableMetaForm(m, _, gs), t2) =>
        trySolve(m, gs, t2)
      case (t1, SolvableMetaForm(m, _, gs)) =>
        trySolve(m, gs, t1)
      case _ => unifyFailed()
    }
  }

  def recValueSystem(t: Value, r1: ValueSystem, r2: ValueSystem): Boolean = {
    forCompatibleAssignments(r1, r2) { (a, b1, b2) =>
      recTerm(t.restrict(a), b1.restrict(a), b2.restrict(a))
    }
  }

  def recGlueFaces(t: Value, r1: ValueSystem, r2: ValueSystem): Boolean = {
    recValueSystem(App(BuiltIn.equiv_of, t), r1, r2)
  }

  private def recCases(domain: Value, codomain: Closure, c1: Seq[Case], c2: Seq[Case]): Boolean = {
    c1.size == c2.size && c1.zip(c2).forall(pair => {
      pair._1.pattern == pair._2.pattern && {
        Try { extractTypes(pair._1.pattern, domain) } match {
          case Success((vs, ds, itself)) =>
            recTerm(codomain(itself), pair._1.closure(vs, ds), pair._2.closure(vs, ds))
          case _ => unifyFailedFalse()
        }
      }
    })
  }


  @inline def recGraphValuePart(ns: ClosureGraph, t1: Int => Value, t2: Int => Value): Boolean = {
    ns.graph.indices.foldLeft(Some(ns) : Option[ClosureGraph]) { (as0, i) =>
      as0 match {
        case Some(as) =>
          val m1 = t1(i)
          if (recTerm(as(i).independent.typ, m1, t2(i))) {
            Some(as.reduce(i, m1))
          } else {
            unifyFailed()
          }
        case None =>
          unifyFailed()
      }
    }
  }

  /**
    * it is REQUIRED that t1 and t2 indeed has that type!!!!
    * FIXME what impact will there be if unification is not type directed?
    */
  private def recTerm(typ: Value, t1: Value, t2: Value): Boolean = {
    if (t1.eq(t2)) {
      true
    } else {
      (typ.whnf, t1.whnf, t2.whnf) match {
        case (Function(d, _, cd), s1, s2) =>
          val c = Generic(gen(), d)
          recTerm(cd(c), App(s1, c), App(s2, c))
        case (PathType(ty, _, _), s1, s2) =>
          val c = Formula.Generic(dgen())
          recTerm(ty(c), PathApp(s1, c), PathApp(s2, c))
        case (r: Record, m1, m2) =>
          recGraphValuePart(r.nodes, i => Projection(m1, i), i => Projection(m2, i))
        case (s: Sum, Construct(n1, v1, d1, _), Construct(n2, v2, d2, _)) =>
          n1 == n2 && { val c = s.constructors(n1) ;
            assert(c.nodes.size == v1.size && c.nodes.dimSize == d1.size && v2.size == v1.size && d1.size == d2.size)
            recGraphValuePart(c.nodes, v1, v2) && d1.zip(d2).forall(p => p._1.normalForm == p._2.normalForm)
          }
        case (g: GlueType, t1, t2) =>
          def baseCase(a: Glue, b: Glue): Boolean = {
            val Glue(m1, r1) = a
            val Glue(m2, r2) = a
            recTerm(g.ty, m1, m2) && forCompatibleAssignments(g.faces, r1, r2) { (a, bt, b1, b2) =>
              recTerm(
                Projection(bt.restrict(a), 0),
                b1.restrict(a),
                b2.restrict(a)
              )
            }
          }
          def deunglue(a: Value): Value = a match {
            case g: Glue =>
              g.m.whnf match {
                case Unglue(_, base, _) => deunglue(base.whnf)
                case _ => a
              }
            case _ => g
          }
          // FIXME is this correct? what about eta for glue?
          (deunglue(t1), deunglue(t2)) match {
            case (g1: Glue, g2: Glue) => baseCase(g1, g2)
            case (a, b) => recNeutral(a, b)
          }
        case (Universe(_), tt1, tt2) =>
          recType(tt1, tt2) // it will call unify neutral at then end
        case (_, tt1, tt2) => recNeutral(tt1, tt2)
      }
    }
  }

  private def extractTypes(
                            pattern: Pattern,
                            typ: Value
                          ): (Seq[Generic], Seq[Formula.Generic], Value) = {
    val vs = mutable.ArrayBuffer[Generic]()
    val ds = mutable.ArrayBuffer[Formula.Generic]()

    def recs(maps: Seq[Pattern], graph0: ClosureGraph): (Seq[Value], ClosureGraph)  = {
      var graph = graph0
      var vs =  Seq.empty[Value]
      for (i  <- maps.indices) {
        val it = graph(i).independent.typ
        val tv = rec(maps(i), it)
        graph = graph.reduce(i, tv)
        vs = vs :+ tv
      }
      (vs, graph)
    }

    def rec(p: Pattern, t: Value): Value = {
      p match {
        case Pattern.GenericValue =>
          val ret = Generic(gen(), t)
          vs.append(ret)
          ret
        case Pattern.GenericDimension => logicError()
        case Pattern.Make(maps) =>
          t.whnf match {
            case r: Record  =>
              if (maps.size == r.nodes.size) {
                Make(recs(maps, r.nodes)._1)
              } else {
                logicError()
              }
            case _ => logicError()
          }
        case Pattern.Construct(name, maps) =>
          t.whnf match {
            case sum: Sum =>
              val c = sum.constructors(name)
              if (c.nodes.dimSize + c.nodes.size == maps.size) {
                val ret = (0 until c.nodes.dimSize).map(_ => Formula.Generic(dgen()))
                ds.appendAll(ret)
                val (vs, cl) = recs(maps.take(c.nodes.size), c.nodes)
                Construct(name, vs, ret, if (ret.size == 0) Map.empty else cl.reduce(ret).restrictions())
              } else {
                logicError()
              }
            case _ => logicError()
          }
      }
    }
    val t = rec(pattern, typ)
    (vs.toSeq, ds.toSeq, t)
  }
}
