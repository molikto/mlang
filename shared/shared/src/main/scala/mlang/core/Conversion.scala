package mlang.core

import Value._

import scala.collection.mutable
import scala.util.{Success, Try}

// TODO is it true what one step reduction with default reduction is terminating?
// TODO is our way of handling recursive definitions sound? (id pattern lambda, with assumptions)
class Conversion {


  // TODO seems this can be globally shared
  private val assumps = new mutable.HashMap[Long, mutable.Set[Long]] with mutable.MultiMap[Long, Long]


  private def equalPatternLambdaOfSameTypeWithAssumptions(domain: Value, l1: PatternLambda, l2: PatternLambda): Boolean = {
    if (l1.id == l2.id) {
      true
    } else {
      if (assumps.entryExists(l1.id, _ == l2.id)) {
        true
      } else {
        assumps.addBinding(l1.id, l2.id)
        equalCases(domain, l1.typ, l1.cases, l2.cases)
      }
    }
  }

  private val reduction = Reduction.Default
  private val gen: GenericGen = new GenericGen.Negative()
  private val dgen: GenericGen = new GenericGen.Negative()

  private implicit def optToBool[T](opt: Option[T]): Boolean = opt.isDefined

  private def equalRecordFields(less: Int, n1: Seq[RecordNode], n2: Seq[RecordNode]): Boolean = {
    if (n1.map(_.name) == n2.map(_.name)) {
      n1.zip(n2).foldLeft(Some(Seq.empty[Value]) : Option[Seq[Value]]) { (as0, pair) =>
        as0 match {
          case Some(as) if pair._1.dependencies == pair._2.dependencies =>
            val mm = n1.map(_.name.refSelf).zip(as).toMap
            equalTypeMultiClosure(less, pair._1.dependencies.map(mm), pair._1.closure, pair._2.closure).map(as :+ _)
          case None =>
            None
        }
      }
    } else {
      false
    }
  }

  private def equalConstructor(less: Int, c1: Constructor, c2: Constructor): Boolean = {
    if (c1.eq(c2)) {
      true
    } else {
      c1.name == c2.name && c1.parameters == c2.parameters && c1.nodes.size == c2.nodes.size && c1.nodes.zip(c2.nodes).foldLeft(Some(Seq.empty[Value]) : Option[Seq[Value]]) { (as0, pair) =>
          as0 match {
            case Some(as) =>
              equalTypeMultiClosure(less, as, pair._1, pair._2).map(as :+ _)
            case None =>
              None
          }
      }
    }
  }



  private def equalTypeMultiClosure(less: Int, ts: Seq[Value], c1: MultiClosure, c2: MultiClosure): Option[Value] = {
    val cs = ts.map(t => OpenReference(gen(), t))
    val t = c1(cs, reduction)
    if (equalType(less, t, c2(cs, reduction))) {
      Some(t)
    } else {
      None
    }
  }

  private def equalTypeClosure(less: Int, t: Value, c1: Closure, c2: Closure): Option[Value] = {
    val c = OpenReference(gen(), t)
    val tt = c1(c, reduction)
    if (equalType(less, tt, c2(c, reduction))) {
      Some(tt)
    } else {
      None
    }
  }

  private def equalType(less: Int, tm1: Value, tm2: Value): Boolean = {
    if (tm1.eq(tm2)) {
      true
    } else {
      (tm1, tm2) match {
        case (Function(d1, c1), Function(d2, c2)) =>
          equalType(less, d1, d2) && equalTypeClosure(less, d1, c1, c2)
        case (Universe(l1), Universe(l2)) =>
          l1 == l2 && l1 <= less
        case (Record(l1, n1), Record(l2, n2)) =>
          l1 == l2 && l1 <= less && equalRecordFields(l1, n1, n2)
        case (Sum(l1, c1), Sum(l2, c2)) =>
          l1 == l2 && l1 <= less && c1.size == c2.size && c1.zip(c2).forall(p => equalConstructor(l1, p._1, p._2))
        case (PathType(t1, l1, r1), PathType(t2, l2, r2)) =>
          val a = t1(Value.Dimension.Constant(false))
          val b = t2(Value.Dimension.Constant(false))
          // we can call equal term here because we know tm1 and tm2 is well typed
          if (equalType(less, a, b) && equalTerm(a, l1, l2)) {
            val c = t1(Value.Dimension.Constant(true))
            val d = t2(Value.Dimension.Constant(true))
            equalType(less, c, d) && equalTerm(c, r1, r2)
          } else {
            false
          }
        case (t1, t2) =>
          equalNeutral(t1, t2) match {
            case Some(Universe(l)) => l <= less
            case _ => false
          }
      }
    }
  }



  private def equalNeutral(t1: Value, t2: Value): Option[Value] = {
    (t1, t2) match {
      case (OpenReference(i1, v1), OpenReference(i2, v2)) =>
        if (i1 == i2) {
          assert(v1.eq(v2))
          Some(v1)
        } else {
          None
        }
      case (Application(l1, a1), Application(l2, a2)) =>
        equalNeutral(l1, l2).flatMap {
          case Function(d, c) =>
          if (equalTerm(d, a1, a2)) {
            Some(c(a1))
          } else {
            None
          }
          case _ => throw new IllegalArgumentException("")
        }
      case (Projection(m1, f1), Projection(m2, f2)) =>
        equalNeutral(m1, m2).flatMap {
          case r: Record if f1 == f2 => Some(r.projectedType(r.nodes.indices.map(n => Projection(m1, n)), f2))
          case _ => throw new IllegalArgumentException("")
        }
      case (PatternStuck(l1, s1), PatternStuck(l2, s2)) =>
        equalNeutral(s1, s2).flatMap(n => {
          // TODO give an example why this is needed
          if (equalTypeClosure(Int.MaxValue, n, l1.typ, l2.typ) && equalPatternLambdaOfSameTypeWithAssumptions(n, l1, l2)) {
            Some(l1.typ(n))
          } else {
            None
          }
        })
      case (PathApplication(l1, d1), PathApplication(l2, d2)) =>
        if (d1 == d2) {
          equalNeutral(l1, l2).map(_ match {
            case PathType(typ, _, _) =>
              typ(d1)
            case _ => throw new IllegalArgumentException("")
          })
        } else {
          None
        }
      case _ => None
    }
  }

  private def equalCases(domain: Value, codomain: Value.Closure, c1: Seq[Case], c2: Seq[Case]): Boolean = {
    c1.size == c2.size && c1.zip(c2).forall(pair => {
      pair._1.pattern == pair._2.pattern && {
        Try { Value.extractTypes(pair._1.pattern, domain, gen) } match {
          case Success((ctx, itself)) =>
            equalTerm(codomain(itself), pair._1.closure(ctx, reduction), pair._2.closure(ctx, reduction))
          case _ => false
        }
      }
    })
  }

  /**
    * it is REQUIRED that t1 and t2 indeed has that type!!!!
    */
  private def equalTerm(typ: Value, t1: Value, t2: Value): Boolean = {
    if (t1.eq(t2)) {
      true
    } else {
      (typ, t1, t2) match {
        case (Function(d, cd), s1, s2) =>
          val c = OpenReference(gen(), d)
          equalTerm(cd(c), s1.app(c, reduction), s2.app(c, reduction))
        case (PathType(typ, _, _), s1, s2) =>
          val c = Dimension.OpenReference(dgen())
          equalTerm(typ(c), s1.papp(c, reduction), s2.papp(c, reduction))
        case (Record(_, ns), m1, m2) =>
          ns.zipWithIndex.foldLeft(Some(Seq.empty) : Option[Seq[Value]]) { (as0, pair) =>
            as0 match {
              case Some(as) =>
                val mm = ns.map(_.name.refSelf).zip(as).toMap
                val nm = pair._1.closure(pair._1.dependencies.map(mm))
                if (equalTerm(nm, m1.project(pair._2, reduction), m2.project(pair._2, reduction))) {
                  Some(as :+ nm)
                } else {
                  None
                }
              case None =>
                None
            }
          }
        case (Sum(_, cs), Construct(n1, v1), Construct(n2, v2)) =>
          n1 == n2 && cs.find(_.name == n1).exists(c => {
            assert(c.nodes.size == v1.size && v2.size == v1.size)
            c.nodes.zip(v1.zip(v2)).foldLeft(Some(Seq.empty): Option[Seq[Value]]) { (as0, pair) =>
              as0 match {
                case Some(as) =>
                  val nm = pair._1(as)
                  if (equalTerm(nm, pair._2._1, pair._2._2)) {
                    Some(as :+ nm)
                  } else {
                    None
                  }
                case None =>
                  None
              }
            }
          })
        case _ =>
          typ match {
            case Universe(l) => equalType(l, t1, t2) // it will call equal neutral at then end
            case _ => equalNeutral(t1, t2)
          }
      }
    }
  }
}

object Conversion {
  def equalTerm(typ: Value, t1: Value, t2: Value): Boolean = {
    new Conversion().equalTerm(typ, t1, t2)
  }

  def equalType(less: Int, tm1: Value, tm2: Value): Boolean = {
    new Conversion().equalType(less, tm1, tm2)
  }
}
