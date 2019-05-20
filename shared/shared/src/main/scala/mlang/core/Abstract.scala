package mlang.core

import mlang.name._

case class Dependency(i: Int, meta: Boolean)

sealed trait Abstract {

  import Abstract._

  def termDependencies(i: Int): Set[Int] = dependencies(i).flatMap {
    case Dependency(i, false) => Set(i)
    case _ => Set.empty[Int]
  }

  def dependencies(i: Int): Set[Dependency] = this match {
    case Universe(_) => Set.empty
    //case Reference(up, index) => if (i == up) Set(index) else Set.empty
    //case MetaReference(up, index) => Set.empty
    case Reference(up, index) => if (i == up) Set(Dependency(index, false)) else Set.empty
    case MetaReference(up, index) => if (i == up) Set(Dependency(index, true)) else Set.empty
    case Function(domain, codomain) => domain.dependencies(i) ++ codomain.dependencies(i)
    case Lambda(closure) => closure.dependencies(i)
    case App(left, right) => left.dependencies(i) ++ right.dependencies(i)
    case Record(_, _, nodes) => nodes.flatMap(_._2.dependencies(i)).toSet
    case Projection(left, _) => left.dependencies(i)
    case Sum(_, constructors) => constructors.flatMap(_.params.flatMap(_._2.dependencies(i))).toSet
    case Maker(sum, _) => sum.dependencies(i)
    case Let(metas, definitions, in) =>
      metas.flatMap(a => a.dependencies(i + 1)).toSet  ++ definitions.flatMap(a => a.dependencies(i + 1)).toSet ++ in.dependencies(i + 1)
    case PatternLambda(_, cd, cases) => cd.dependencies(i) ++ cases.flatMap(_.body.dependencies(i)).toSet
    case PathLambda(body) => body.dependencies(i)
    case PathType(typ, left, right) => typ.dependencies(i) ++ left.dependencies(i) ++ right.dependencies(i)
    case PathApp(lef, _) => lef.dependencies(i)
    case Coe(_, tp, base) => tp.dependencies(i) ++ base.dependencies(i)
    case Hcom(_, tp, base, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ faces.flatMap(_.dependencies(i)).toSet
    case Com(_, tp, base, faces) => tp.dependencies(i + 1) ++ base.dependencies(i) ++ faces.flatMap(_.dependencies(i)).toSet
    case Restricted(term, _) => term.dependencies(i)
  }
}

// abstract terms will have restricted terms annotated
object Abstract {

  sealed trait MetaEnclosedT {
    val term: Abstract
    val metas: Seq[Abstract]
    def dependencies(i: Int): Set[Dependency] = term.dependencies(i + 1)
  }
  sealed trait ClosureT extends MetaEnclosedT {
  }

  case class Closure(metas: Seq[Abstract], term: Abstract) extends ClosureT
  case class AbsClosure(metas: Seq[Abstract], term: Abstract) extends ClosureT
  case class MultiClosure(metas: Seq[Abstract], term: Abstract) extends ClosureT
  case class MetaEnclosed(metas: Seq[Abstract], term: Abstract) extends MetaEnclosedT // used by closure graph


  type ClosureGraph = Seq[(Seq[Int], MetaEnclosed)]

  case class Universe(i: Int) extends Abstract

  case class Reference(up: Int, index: Int) extends Abstract

  case class MetaReference(up: Int, index: Int) extends Abstract

  case class Function(domain: Abstract, codomain: Closure) extends Abstract

  case class Lambda(closure: Closure) extends Abstract

  case class App(left: Abstract, right: Abstract) extends Abstract

  case class Record(level: Int, names: Seq[Name], graph: ClosureGraph) extends Abstract

  case class Projection(left: Abstract, field: Int) extends Abstract

  case class Constructor(name: Name, params: ClosureGraph)

  case class Sum(level: Int, constructors: Seq[Constructor]) extends Abstract


  case class Maker(sum: Abstract, field: Int) extends Abstract

  case class Let(metas: Seq[Abstract], definitions: Seq[Abstract], in: Abstract) extends Abstract

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
  case class Face(pair: DimensionPair, body: AbsClosure) {
    def dependencies(i: Int): Set[Dependency] = body.dependencies(i + 1)
  }

  case class DimensionPair(from: Dimension, to: Dimension)

  sealed trait Dimension
  object Dimension {
    case class Reference(up: Int) extends Dimension
    case object True extends Dimension
    case object False extends Dimension
    case class Restricted(a: Dimension, restriction: DimensionPair) extends Dimension
  }
}
