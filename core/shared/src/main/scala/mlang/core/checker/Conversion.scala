package mlang.core.checker

import Value._

import scala.util.{Success, Try}

trait Conversion extends Context {

  private val gen: GenericGen = GenericGen.Negative

  private def equalRecordFields(less: Int, n1: Seq[RecordNode], n2: Seq[RecordNode]): Boolean = {
    if (n1.map(_.name) == n2.map(_.name)) {
      n1.zip(n2).foldLeft(Some(Seq.empty[Value]) : Option[Seq[Value]]) { (as0, pair) =>
        as0 match {
          case Some(as) if pair._1.dependencies == pair._2.dependencies =>
            val mm = n1.map(_.name).zip(as).toMap
            equalTypeMultiClosure(less, pair._1.dependencies.map(mm), pair._1.closure, pair._2.closure).map(as :+ _)
          case None =>
            None
        }
      }.isDefined
    } else {
      false
    }
  }

  private def equalConstructor(less: Int, c1: Constructor, c2: Constructor): Boolean = {
    if (c1.eq(c2)) {
      true
    } else {
      c1.name == c2.name && c1.nodes.size == c2.nodes.size && c1.nodes.zip(c2.nodes).foldLeft(Some(Seq.empty[Value]) : Option[Seq[Value]]) { (as0, pair) =>
          as0 match {
            case Some(as) =>
              equalTypeMultiClosure(less, as, pair._1, pair._2).map(as :+ _)
            case None =>
              None
          }
      }.isDefined
    }
  }



  private def equalTypeMultiClosure(less: Int, ts: Seq[Value], c1: MultiClosure, c2: MultiClosure): Option[Value] = {
    val cs = ts.map(t => OpenReference(gen(), t, ""))
    val t = c1(cs)
    if (equalType(less, t, c2(cs))) {
      Some(t)
    } else {
      None
    }
  }

  private def equalTypeClosure(less: Int, t: Value, c1: Closure, c2: Closure): Boolean = {
    if (c1.eq(c2)) {
      true
    } else {
      val c = OpenReference(gen(), t, "")
      equalType(less, c1(Seq(c)), c2(Seq(c)))
    }
  }

  private def equalValueClosure(domain: Value, codomain: Closure, c1: Closure, c2: Closure): Boolean = {
    if (c1.eq(c2)) {
      true
    } else {
      val c = OpenReference(gen(), domain, "")
      equalTerm(codomain(Seq(c)), c1(Seq(c)), c2(Seq(c)))
    }
  }


  private def equalNeutral(t1: Value, t2: Value): Option[Value] = {
    (t1, t2) match {
      case (OpenReference(i1, v1, _), OpenReference(i2, v2, _)) =>
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
            Some(c(Seq(a1)))
          } else {
            None
          }
          case _ => throw new IllegalArgumentException("")
        }
      case (Projection(m1, f1), Projection(m2, f2)) =>
        equalNeutral(m1, m2).flatMap {
          case r: Record if f1 == f2 => Some(r.projectedType((0 until r.nodes.size).map(n => Projection(m1, n)), f2))
          case _ => throw new IllegalArgumentException("")
        }
      case (PatternStuck(l1, s1), PatternStuck(l2, s2)) =>
        equalNeutral(s1, s2).flatMap(n => {
          if (equalTerm(Function(n, l1.typ), l1, l2)) {
            Some(l1.typ(Seq(n)))
          } else {
            None
          }
        })
      case _ => None
    }
  }


  protected def equalType(less: Int, tm1: Value, tm2: Value): Boolean = {
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
        case (t1, t2) =>
          equalNeutral(t1, t2) match {
            case Some(Universe(l)) => l <= less
            case _ => false
          }
      }
    }
  }

  private def equalTerm(typ: Value, t1: Value, t2: Value): Boolean = {
    if (t1.eq(t1)) {
      true
    } else {
      (typ, t1, t2) match {
        case (Function(d, cd), Lambda(c1), Lambda(c2)) =>
          equalValueClosure(d, cd, c1, c2)
        case (Record(_, ns), Make(v1), Make(v2)) =>
          ns.size == v1.size && ns.size == v2.size && ns.zip(v1.zip(v2)).foldLeft(Some(Seq.empty) : Option[Seq[Value]]) { (as0, pair) =>
            as0 match {
              case Some(as) =>
                val mm = ns.map(_.name).zip(as).toMap
                val nm = pair._1.closure(pair._1.dependencies.map(mm))
                if (equalTerm(nm, pair._2._1, pair._2._2)) {
                  Some(as :+ nm)
                } else {
                  None
                }
              case None =>
                None
            }
          }.isDefined
        case (Sum(_, cs), Construct(n1, v1), Construct(n2, v2)) =>
          n1 == n2 && cs.find(_.name == n1).exists(c => {
            if (c.nodes.size == v1.size && v2.size == v1.size) {
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
              }.isDefined
            } else {
              false
            }
          })
        case (Function(domain, codomain), PatternLambda(_, c1), PatternLambda(_, c2)) =>
          // TODO is it needed to check lambda type is equal?
          c1.size == c2.size && c1.zip(c2).forall(pair => {
             pair._1.pattern == pair._2.pattern && {
               Try { Value.extractTypes(pair._1.pattern, domain, gen) } match {
                 case Success((ctx, itself)) =>
                   equalTerm(codomain(Seq(itself)), pair._1.closure(ctx), pair._2.closure(ctx))
                 case _ => false
               }
             }
          })
        case _ =>
          typ match {
            case Universe(l) => equalType(l, t1, t2) // it will call equal neutral at then end
            case _ => equalNeutral(t1, t2).isDefined
          }
      }
    }
  }
}
