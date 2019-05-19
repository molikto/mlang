package mlang.core

import mlang.name._


sealed trait Abstract {

  import Abstract._
  def markRecursive(i: Int, c: Set[Int]): Unit = this match {
    case Universe(_) => 
    case r@TermReference(up, _, _) =>
      r.closed = up == i
//      if (up == i) {
//        if (c.contains(index)) {
//          r.closed = 1
//        } else {
//          r.closed = 0
//        }
//      }
    case Function(domain, codomain) =>
      domain.markRecursive(i, c)
      codomain.markRecursive(i + 1, c)
    case Lambda(closure) =>
      closure.markRecursive(i + 1, c)
    case App(left, right) =>
      left.markRecursive(i, c)
      right.markRecursive(i, c)
    case Record(_, ns, nodes) =>
      nodes.foreach(_._2.markRecursive(i + 1, c))
    case Projection(left, _) =>
      left.markRecursive(i, c)
    case Sum(_, constructors) =>
      constructors.foreach(_.params.foreach(_._2.markRecursive(i + 1, c)))
    case Maker(sum, _) =>
      sum.markRecursive(i, c)
    case Let(definitions, _, in) =>
      definitions.foreach(a => {
        a.markRecursive(i + 1, c)
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
    case PathApp(lef, _) =>
      lef.markRecursive(i, c)
    case Coe(_, tp, base) =>
      tp.markRecursive(i + 1, c)
      base.markRecursive(i, c)
    case Com(_, tp, base, faces) =>
      tp.markRecursive(1 + i, c)
      base.markRecursive(i, c)
      faces.foreach(_.body.markRecursive(i + 2, c))
    case Hcom(_, tp, base, faces) =>
      tp.markRecursive(i, c)
      base.markRecursive(i, c)
      faces.foreach(_.body.markRecursive(i + 2, c))
    case Restricted(term, _) =>
      term.markRecursive(i, c)
  }

  def dependencies(i: Int): Set[Int] = this match {
    case Universe(_) => Set.empty
    case TermReference(up, index, _) => if (i == up) Set(index) else Set.empty
    case Function(domain, codomain) => domain.dependencies(i) ++ codomain.dependencies(i + 1)
    case Lambda(closure) => closure.dependencies(i + 1)
    case App(left, right) => left.dependencies(i) ++ right.dependencies(i)
    case Record(_, _, nodes) => nodes.flatMap(_._2.dependencies(i + 1)).toSet
    case Projection(left, _) => left.dependencies(i)
    case Sum(_, constructors) => constructors.flatMap(_.params.flatMap(_._2.dependencies(i + 1))).toSet
    case Maker(sum, _) => sum.dependencies(i)
    case Let(definitions, _, in) => definitions.flatMap(a => a.dependencies(i + 1)).toSet ++ in.dependencies(i + 1)
    case PatternLambda(_, cd, cases) => cd.dependencies(i + 1) ++ cases.flatMap(_.body.dependencies(i + 1)).toSet
    case PathLambda(body) => body.dependencies(i + 1)
    case PathType(typ, left, right) => typ.dependencies(i + 1) ++ left.dependencies(i) ++ right.dependencies(i)
    case PathApp(lef, _) => lef.dependencies(i)
    case Coe(_, tp, base) => tp.dependencies(i + 1) ++ base.dependencies(i)
    case Hcom(_, tp, base, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ faces.flatMap(_.body.dependencies(i + 2)).toSet
    case Com(_, tp, base, faces) => tp.dependencies(i + 1) ++ base.dependencies(i) ++ faces.flatMap(_.body.dependencies(i + 2)).toSet
    case Restricted(term, _) => term.dependencies(i)
  }
}

// abstract terms will have restricted terms annotated
object Abstract {
  type Closure = Abstract
  type MultiClosure = Abstract
  type AbsClosure = Abstract

  type ClosureGraph = Seq[(Seq[Int], MultiClosure)]

  case class Universe(i: Int) extends Abstract

  case class TermReference(up: Int, index: Int, @lateinit var closed: Boolean) extends Abstract

  case class Function(domain: Abstract, codomain: Closure) extends Abstract

  case class Lambda(closure: Closure) extends Abstract

  case class App(left: Abstract, right: Abstract) extends Abstract

  case class Record(level: Int, names: Seq[Name], graph: ClosureGraph) extends Abstract

  case class Projection(left: Abstract, field: Int) extends Abstract

  case class Sum(level: Int, constructors: Seq[Constructor]) extends Abstract

  case class Constructor(name: Name, params: ClosureGraph)

  case class Maker(sum: Abstract, field: Int) extends Abstract

  case class Let(definitions: Seq[Abstract], order: Seq[Int], in: Abstract) extends Abstract

  case class Case(pattern: Pattern, body: MultiClosure)
  case class PatternLambda(id: Long, typ: Closure, cases: Seq[Case]) extends Abstract

  case class PathLambda(body: AbsClosure) extends Abstract
  case class PathType(typ: AbsClosure, left: Abstract, right: Abstract) extends Abstract
  case class PathApp(let: Abstract, r: Dimension) extends Abstract

  case class Coe(direction: DimensionPair, tp: AbsClosure, base: Abstract) extends Abstract
  case class Hcom(direction: DimensionPair, tp: Abstract, base: Abstract, faces: Seq[Face]) extends Abstract

  case class Com(direction: DimensionPair, tp: AbsClosure, base: Abstract, faces: Seq[Face]) extends Abstract

  case class Restricted(term: Abstract, restriction: DimensionPair) extends Abstract

  // restriction doesn't take binding, but they have a level non-the-less
  case class Face(pair: DimensionPair, body: AbsClosure)

  case class DimensionPair(from: Dimension, to: Dimension)

  sealed trait Dimension
  object Dimension {
    case class Reference(up: Int) extends Dimension
    case object True extends Dimension
    case object False extends Dimension
    case class Restricted(a: Dimension, restriction: DimensionPair) extends Dimension
  }
}
