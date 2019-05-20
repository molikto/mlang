package mlang.core

import Value._
import mlang.utils.{Benchmark, debug}

import scala.collection.mutable
import scala.util.{Success, Try}

private case class Assumption(left: Long, right: Long, domain: Value, codomain: Closure)



object Unify {
  def unifyTerm(typ: Value, t1: Value, t2: Value): Boolean = {
    Benchmark.ConversionChecking {
      new Unify().unifyTerm(typ, t1, t2)
    }
  }

  def unifyType(tm1: Value, tm2: Value): Boolean = {
    Benchmark.ConversionChecking {
      new Unify().unifyType(tm1, tm2)
    }
  }
}


class Unify {

  // TODO this is potentially non-terminating now, if the domain/codomain changes each time, this can happens for indexed types I think
  private val patternAssumptions = mutable.ArrayBuffer[Assumption]()

  // TODO handle parameterized recursively defined ones, we should only allow them in top level, and make recursive reference non-reducible?
  private val typeAssumptions = mutable.ArrayBuffer[(Value, Value)]()

  private def unifySameTypePatternLambdaWithAssumptions(domain: Value, l1: PatternLambda, l2: PatternLambda): Boolean = {
    if (l1.id == l2.id) {
      true
    } else {
      if (patternAssumptions.exists(a => a.left == l1.id && a.right == l2.id && unifyType(a.domain, domain) && unifyTypeClosure(a.domain, a.codomain, l1.typ))) {
        true
      } else {
        patternAssumptions.append(Assumption(l1.id, l2.id, domain, l1.typ))
        unifyCases(domain, l1.typ, l1.cases, l2.cases)
      }
    }
  }

  private val gen: LongGen = new LongGen.Negative()
  private val dgen: LongGen = new LongGen.Negative()

  private implicit def optToBool[T](opt: Option[T]): Boolean = opt.isDefined

  private def unifyClosureGraph(n1: ClosureGraph, n2: ClosureGraph): Boolean = {
    n1.size == n2.size && {
      var g1 = n1
      var g2 = n2
      var eq = true
      var i = 0
      while (i < n1.size && eq) {
        val t1 = g1(i).independent.typ
        val t2 = g2(i).independent.typ
        eq = unifyType(t1, t2)
        val g = Generic(gen(), t1)
        g1 = ClosureGraph.reduce(g1, i, g)
        g2 = ClosureGraph.reduce(g2, i, g)
        i += 1
      }
      eq
    }
  }

  private def unifyConstructor(c1: Constructor, c2: Constructor): Boolean = {
    if (c1.eq(c2)) {
      true
    } else {
      c1.name == c2.name && unifyClosureGraph(c1.nodes, c2.nodes)
    }
  }



  private def unifyTypeClosure(t: Value, c1: Closure, c2: Closure): Option[Value] = {
    val c = Generic(gen(), t)
    val tt = c1(c)
    if (unifyType(tt, c2(c))) {
      Some(tt)
    } else {
      None
    }
  }

  private def unifyAbsClosure(typ: Value, t1: AbsClosure, t2: AbsClosure): Boolean = {
    val c = Dimension.Generic(dgen())
    unifyTerm(typ, t1(c), t2(c))
  }


  private def unifyTypeAbsClosure(t1: AbsClosure, t2: AbsClosure): Boolean = {
    val c = Dimension.Generic(dgen())
    unifyType(t1(c), t2(c))
  }


  private def unifyType(tm1: Value, tm2: Value): Boolean = {
    if (tm1.eq(tm2)) {
      true
    } else if (typeAssumptions.exists(a => a._1.eq(tm1) && a._2.eq(tm2))) { // recursive defined sum and record
      true
    } else {
      typeAssumptions.append((tm1, tm2))
      (tm1.whnf, tm2.whnf) match {
        case (Function(d1, c1), Function(d2, c2)) =>
          unifyType(d1, d2) && unifyTypeClosure(d1, c1, c2)
        case (Universe(l1), Universe(l2)) =>
          l1 == l2
        case (Record(l1, m1, n1), Record(l2, m2, n2)) =>
          l1 == l2 && m1 == m2 && unifyClosureGraph(n1, n2)
        case (Sum(l1, c1), Sum(l2, c2)) =>
          l1 == l2 && c1.size == c2.size && c1.zip(c2).forall(p => unifyConstructor(p._1, p._2))
        case (PathType(t1, l1, r1), PathType(t2, l2, r2)) =>
          unifyTypeAbsClosure(t1, t2) &&
              unifyTerm(t1(Dimension.False), l1, l2) &&
              unifyTerm(t1(Dimension.True), r1, r2)
        case (t1, t2) =>
          unifyNeutral(t1, t2).map(_.whnf match {
            case Universe(_) => true
            case _ => false
          })
      }
    }
  }



  private def unifyNeutral(tmm1: Value, tmm2: Value): Option[Value] = {
    (tmm1.whnf, tmm2.whnf) match {
      case (Generic(i1, v1), Generic(i2, v2)) =>
        if (i1 == i2) {
          if (debug.enabled) {
            if (!unifyType(v1, v2)) {
              logicError()
            }
          }
          Some(v1)
        } else {
          None
        }
      case (App(l1, a1), App(l2, a2)) =>
        unifyNeutral(l1, l2).map(_.whnf).flatMap {
          case Function(d, c) =>
          if (unifyTerm(d, a1, a2)) {
            Some(c(a1))
          } else {
            None
          }
          case _ => logicError()
        }
      case (Projection(m1, f1), Projection(m2, f2)) =>
        unifyNeutral(m1, m2).map(_.whnf).flatMap {
          case r: Record if f1 == f2 => Some(r.projectedType(r.nodes.indices.map(n => Projection(m1, n)), f2))
          case _ => logicError()
        }
      case (PatternStuck(l1, s1), PatternStuck(l2, s2)) =>
        unifyNeutral(s1, s2).flatMap(n => {
          if (unifyTypeClosure(n, l1.typ, l2.typ) && unifySameTypePatternLambdaWithAssumptions(n, l1, l2)) {
            Some(l1.typ(s1))
          } else {
            None
          }
        })
      case (PathApp(l1, d1), PathApp(l2, d2)) =>
        if (d1 == d2) {
          unifyNeutral(l1, l2).map(_.whnf match {
            case PathType(typ, _, _) =>
              typ(d1)
            case _ => logicError()
          })
        } else {
          None
        }
      case (Hcom(d1, t1, b1, r1), Hcom(d2, t2, b2, r2)) =>
        if (d1 == d2 && unifyType(t1, t2) && unifyTerm(t1, b1, b2)) {
          if (r1.size == r2.size && r1.zip(r2).forall(p => p._1.restriction == p._2.restriction && unifyAbsClosure(t1.restrict(p._1.restriction), p._1.body, p._2.body))) {
            Some(t1)
          } else {
            None
          }
        } else {
          None
        }
      case (Coe(d1, t1, b1), Coe(d2, t2, b2)) =>
        if (d1 == d2 && unifyTypeAbsClosure(t1, t2) && unifyTerm(t1(d1.from), b1, b2)) {
          Some(t1(d1.to))
        } else {
          None
        }
      case _ => None
    }
  }

  private def unifyCases(domain: Value, codomain: Closure, c1: Seq[Case], c2: Seq[Case]): Boolean = {
    c1.size == c2.size && c1.zip(c2).forall(pair => {
      pair._1.pattern == pair._2.pattern && {
        Try { extractTypes(pair._1.pattern, domain) } match {
          case Success((ctx, itself)) =>
            unifyTerm(codomain(itself), pair._1.closure(ctx), pair._2.closure(ctx))
          case _ => false
        }
      }
    })
  }


  @inline def unifyTerms(ns: ClosureGraph, t1: Int => Value, t2: Int => Value): Boolean = {
    ns.indices.foldLeft(Some(ns) : Option[ClosureGraph]) { (as0, i) =>
      as0 match {
        case Some(as) =>
          val m1 = t1(i)
          if (unifyTerm(as(i).independent.typ, m1, t2(i))) {
            Some(ClosureGraph.reduce(as, i, m1))
          } else {
            None
          }
        case None =>
          None
      }
    }
  }

  /**
    * it is REQUIRED that t1 and t2 indeed has that type!!!!
    */
  private def unifyTerm(typ: Value, t1: Value, t2: Value): Boolean = {
    if (t1.eq(t2)) {
      true
    } else {
      (typ.whnf, t1.whnf, t2.whnf) match {
        case (Function(d, cd), s1, s2) =>
          val c = Generic(gen(), d)
          unifyTerm(cd(c), s1.app(c), s2.app(c))
        case (PathType(ty, _, _), s1, s2) =>
          val c = Dimension.Generic(dgen())
          unifyTerm(ty(c), s1.papp(c), s2.papp(c))
        case (Record(_, _, ns), m1, m2) =>
          unifyTerms(ns, i => m1.project(i), i => m2.project(i))
        case (Sum(_, cs), Construct(n1, v1), Construct(n2, v2)) =>
          n1 == n2 && { val c = cs(n1) ;
            assert(c.nodes.size == v1.size && v2.size == v1.size)
            unifyTerms(c.nodes, v1, v2)
          }
        case (Universe(_), tt1, tt2) =>
          unifyType(tt1, tt2) // it will call unify neutral at then end
        case (_, tt1, tt2) => unifyNeutral(tt1, tt2)
      }
    }
  }

  private def extractTypes(
      pattern: Pattern,
      typ: Value
  ): (Seq[Generic], Value) = {
    val vs = mutable.ArrayBuffer[Generic]()

    def recs(maps: Seq[Pattern], graph0: ClosureGraph): Seq[Value]  = {
      var graph = graph0
      var vs =  Seq.empty[Value]
      for (i  <- maps.indices) {
        val it = graph(i).independent.typ
        val tv = rec(maps(i), it)
        graph = ClosureGraph.reduce(graph, i, tv)
        vs = vs :+ tv
      }
      vs
    }

    def rec(p: Pattern, t: Value): Value = {
      p match {
        case Pattern.Atom =>
          val ret = Generic(gen(), t)
          vs.append(ret)
          ret
        case Pattern.Make(maps) =>
          t.whnf match {
            case Record(_, _, nodes) =>
              if (maps.size == nodes.size) {
                Make(recs(maps, nodes))
              } else {
                logicError()
              }
            case _ => logicError()
          }
        case Pattern.Construct(name, maps) =>
          t.whnf match {
            case Sum(_, cs) =>
              val c = cs(name)
              if (c.nodes.size == maps.size) {
                Construct(name, recs(maps, c.nodes))
              } else {
                logicError()
              }
            case _ => logicError()
          }
      }
    }
    val t = rec(pattern, typ)
    (vs, t)
  }
}
