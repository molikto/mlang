package mlang.core.checker

import mlang.core.name._
import mlang.core.varfield



sealed trait Abstract {
  import Abstract._
  def markRecursive(i: Int, c: Set[Int]): Unit = this match {
    case Universe(_) => 
    case r@TermReference(up, index, _) =>
      if (up == i) {
        if (c.contains(index)) {
          r.closed = 1
        } else {
          r.closed = 0
        }
      }
    case Function(domain, codomain) =>
      domain.markRecursive(i, c)
      codomain.markRecursive(i + 1, c)
    case Lambda(closure) =>
      closure.markRecursive(i + 1, c)
    case Application(left, right) =>
      left.markRecursive(i, c)
      right.markRecursive(i, c)
    case Record(_, nodes) =>
      nodes.foreach(_.typ.markRecursive(i + 1, c))
    case RecordMaker(record) =>
      record.markRecursive(i, c)
    case Projection(left, _) =>
      left.markRecursive(i, c)
    case Sum(_, constructors) =>
      constructors.foreach(_.params.foreach(_.markRecursive(i + 2, c)))
    case SumMaker(sum, _) =>
      sum.markRecursive(i, c)
    case Let(definitions, _, in) =>
      definitions.foreach(a => {
        a.value.markRecursive(i + 1, c)
        a.typ.foreach(_.markRecursive(i + 1, c))
      })
      in.markRecursive(i + 1, c)
    case PatternLambda(_, cd, cases) =>
      cd.markRecursive(i + 1, c)
      cases.foreach(_.body.markRecursive(i + 1, c))
    case PathLambda(body) =>
      body.markRecursive(i + 1, c)
    case PathType(typ, left, right) =>
      typ.markRecursive(i + 1, c)
      left.markRecursive(i, c)
      right.markRecursive(i, c)
    case PathApplication(lef, _) =>
      lef.markRecursive(i, c)
  }

  def dependencies(i: Int): Set[Int] = this match {
    case Universe(_) => Set.empty
    case TermReference(up, index, _) => if (i == up) Set(index) else Set.empty
    case Function(domain, codomain) => domain.dependencies(i) ++ codomain.dependencies(i + 1)
    case Lambda(closure) => closure.dependencies(i + 1)
    case Application(left, right) => left.dependencies(i) ++ right.dependencies(i)
    case Record(_, nodes) => nodes.flatMap(_.typ.dependencies(i + 1)).toSet
    case RecordMaker(record) => record.dependencies(i)
    case Projection(left, _) => left.dependencies(i)
    case Sum(_, constructors) => constructors.flatMap(_.params.flatMap(_.dependencies(i + 2))).toSet
    case SumMaker(sum, _) => sum.dependencies(i)
    case Let(definitions, _, in) => definitions.flatMap(a =>
      a.value.dependencies(i + 1) ++ a.typ.map(_.dependencies(i + 1)).getOrElse(Set.empty)).toSet ++ in.dependencies(i + 1)
    case PatternLambda(_, cd, cases) => cd.dependencies(i + 1) ++ cases.flatMap(_.body.dependencies(i + 1)).toSet
    case PathLambda(body) => body.dependencies(i + 1)
    case PathType(typ, left, right) => typ.dependencies(i + 1) ++ left.dependencies(i) ++ right.dependencies(i)
    case PathApplication(lef, _) => lef.dependencies(i)
  }
}

object Abstract {
  case class Universe(i: Int) extends Abstract

  /* -1: formal, 0: closed, 1: closed & recursive */
  case class TermReference(up: Int, index: Int, @varfield var closed: Int  = -1) extends Abstract

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

  object Let {
    case class Item(value: Abstract, typ: Option[Abstract])
  }
  case class Let(definitions: Seq[Let.Item], order: Seq[Set[Int]], in: Abstract) extends Abstract

  case class Case(pattern: Pattern, body: Abstract)
  case class PatternLambda(id: Generic, typ: Abstract, cases: Seq[Case]) extends Abstract {
    override def toString: String = s"PatternLambda(${cases.toString})"
  }

  case class PathLambda(body: Abstract) extends Abstract
  case class PathType(typ: Abstract, left: Abstract, right: Abstract) extends Abstract
  case class PathApplication(let: Abstract, r: Dimension) extends Abstract

  case class Coe(direction: DimensionPair, tp: Abstract, base: Abstract) extends Abstract
  case class Hcom(direction: DimensionPair, tp: Abstract, base: Abstract) extends Abstract

  case class DimensionPair(from: Dimension, to: Dimension)

  sealed trait Dimension
  object Dimension {
    case class Reference(up: Int) extends Dimension
    case class Constant(isOne: Boolean) extends Dimension
  }
}
