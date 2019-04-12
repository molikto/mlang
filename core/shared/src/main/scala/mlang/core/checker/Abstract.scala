package mlang.core.checker

import mlang.core.name._
import mlang.core.varfield


sealed trait Abstract {
  def markRecursive(i: Int, c: Set[Int]): Unit = this match {
    case Abstract.Universe(_) => 
    case r@Abstract.Reference(up, index, _) => 
      if (up == i) {
        if (c.contains(index)) {
          r.closed = 1
        } else {
          r.closed = 0
        }
      }
    case Abstract.Function(domain, codomain) =>
      domain.markRecursive(i, c)
      codomain.markRecursive(i + 1, c)
    case Abstract.Lambda(closure) =>
      closure.markRecursive(i + 1, c)
    case Abstract.Application(left, right) =>
      left.markRecursive(i, c)
      right.markRecursive(i, c)
    case Abstract.Record(_, nodes) =>
      nodes.foreach(_.typ.markRecursive(i + 1, c))
    case Abstract.RecordMaker(record) =>
      record.markRecursive(i, c)
    case Abstract.Projection(left, _) =>
      left.markRecursive(i, c)
    case Abstract.Sum(_, constructors) =>
      constructors.foreach(_.params.foreach(_.markRecursive(i + 2, c)))
    case Abstract.SumMaker(sum, _) =>
      sum.markRecursive(i, c)
    case Abstract.Let(definitions, _, in) =>
      definitions.foreach(_.markRecursive(i + 1, c))
      in.markRecursive(i + 1, c)
    case Abstract.PatternLambda(cd, cases) =>
      cd.markRecursive(i + 1, c)
      cases.foreach(_.body.markRecursive(i + 1, c))
  }

  def dependencies(i: Int): Set[Int] = this match {
    case Abstract.Universe(_) => Set.empty
    case Abstract.Reference(up, index, _) => if (i == up) Set(index) else Set.empty
    case Abstract.Function(domain, codomain) => domain.dependencies(i) ++ codomain.dependencies(i + 1)
    case Abstract.Lambda(closure) => closure.dependencies(i + 1)
    case Abstract.Application(left, right) => left.dependencies(i) ++ right.dependencies(i)
    case Abstract.Record(_, nodes) => nodes.flatMap(_.typ.dependencies(i + 1)).toSet
    case Abstract.RecordMaker(record) => record.dependencies(i)
    case Abstract.Projection(left, _) => left.dependencies(i)
    case Abstract.Sum(_, constructors) => constructors.flatMap(_.params.flatMap(_.dependencies(i + 2))).toSet
    case Abstract.SumMaker(sum, _) => sum.dependencies(i)
    case Abstract.Let(definitions, _, in) => definitions.flatMap(_.dependencies(i + 1)).toSet ++ in.dependencies(i + 1)
    case Abstract.PatternLambda(cd, cases) => cases.flatMap(_.body.dependencies(i + 1)).toSet
  }
}

object Abstract {
  case class Universe(i: Int) extends Abstract

  /* -1: formal, 0: closed, 1: closed & recursive */
  case class Reference(up: Int, index: Int, @varfield var closed: Int  = -1) extends Abstract

  case class Function(domain: Abstract, codomain: Abstract) extends Abstract

  case class Lambda(closure: Abstract) extends Abstract

  case class Application(left: Abstract, right: Abstract) extends Abstract

  case class RecordNode(name: Name, typ: Abstract)
  case class Record(level: Int, nodes: Seq[RecordNode]) extends Abstract

  case class RecordMaker(record: Abstract) extends Abstract

  case class Projection(left: Abstract, field: Int) extends Abstract

  case class Constructor(name: Tag, params: Seq[Abstract])
  case class Sum(level: Int, constructors: Seq[Constructor]) extends Abstract

  case class SumMaker(sum: Abstract, field: Int) extends Abstract

  case class Let(definitions: Seq[Abstract], order: Seq[Set[Int]], in: Abstract) extends Abstract

  case class Case(pattern: Pattern, body: Abstract)
  case class PatternLambda(typ: Abstract, cases: Seq[Case]) extends Abstract {
    override def toString: String = s"PatternLambda(${cases.toString})"
  }
}
