package mlang.core

import mlang.name._

case class Dependency(i: Int, meta: Boolean)

sealed trait Abstract {


  import Abstract._

  def termDependencies(i: Int): Set[Int] = dependencies(i).flatMap {
    case Dependency(i, false) => Set(i)
    case _ => Set.empty[Int]
  }

  def diff(depth: Int, x: Int): Abstract = this match {
    case _: Universe => this
    case Reference(up, index) =>
      if (up > depth) {
        assert(up + x >= 0)
        Reference(up + x, index)
      } else {
        this
      }
    case MetaReference(up, index) =>
      if (up > depth) {
        MetaReference(up + x, index)
      } else {
        this
      }
    case Function(domain, impict, codomain) =>
      Function(domain.diff(depth, x), impict, codomain.diff(depth, x))
    case Lambda(closure) => Lambda(closure.diff(depth, x))
    case App(left, right) => App(left.diff(depth, x), right.diff(depth, x))
    case Record(level, names, implicits, graph) => Record(level, names, implicits, graph.map(a => (a._1, a._2.diff(depth, x))))
    case Projection(left, field) => Projection(left.diff(depth, x), field)
    case Sum(level, constructors) => Sum(level, constructors.map(c => Constructor(c.name, c.implicits, c.params.map(a => (a._1, a._2.diff(depth, x))))))
    case Maker(sum, field) => Maker(sum.diff(depth, x), field)
    case Let(metas, definitions, in) => Let(metas.map(_.diff(depth + 1, x)), definitions.map(_.diff(depth + 1, x)), in.diff(depth + 1, x))
    case PatternLambda(id, typ, cases) => PatternLambda(id, typ.diff(depth, x), cases.map(a => Case(a.pattern, a.body.diff(depth + 1, x))))
    case PathLambda(body) => PathLambda(body.diff(depth, x))
    case PathType(typ, left, right) => PathType(typ.diff(depth, x), left.diff(depth, x), right.diff(depth, x))
    case PathApp(let, r) => PathApp(let.diff(depth, x), r.diff(depth, x))
    case Coe(direction, tp, base) => Coe(direction.diff(depth, x), tp.diff(depth, x), base.diff(depth, x))
    case Hcom(direction, tp, base, faces) => Hcom(direction.diff(depth, x), tp.diff(depth, x), base.diff(depth, x), faces.map(_.diff(depth, x)))
    case Com(direction, tp, base, faces) => Com(direction.diff(depth, x), tp.diff(depth, x), base.diff(depth, x), faces.map(_.diff(depth, x)))
    case Restricted(term, restriction) => Restricted(term.diff(depth, x), restriction.map(_.diff(depth, x)))
  }

  def dependencies(i: Int): Set[Dependency] = this match {
    case Universe(_) => Set.empty
    //case Reference(up, index) => if (i == up) Set(index) else Set.empty
    //case MetaReference(up, index) => Set.empty
    case Reference(up, index) => if (i == up) Set(Dependency(index, false)) else Set.empty
    case MetaReference(up, index) => if (i == up) Set(Dependency(index, true)) else Set.empty
    case Function(domain, _, codomain) => domain.dependencies(i) ++ codomain.dependencies(i)
    case Lambda(closure) => closure.dependencies(i)
    case App(left, right) => left.dependencies(i) ++ right.dependencies(i)
    case Record(_, _, _, nodes) => nodes.flatMap(_._2.dependencies(i)).toSet
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

  case class Closure(metas: Seq[Abstract], term: Abstract) extends ClosureT {
    def diff(depth: Int, x: Int): Closure = Closure(metas.map(_.diff(depth + 1, x)), term.diff(depth + 1, x))
  }

  case class AbsClosure(metas: Seq[Abstract], term: Abstract) extends ClosureT {
    def diff(depth: Int, x: Int): AbsClosure = AbsClosure(metas.map(_.diff(depth + 1, x)), term.diff(depth + 1, x))
  }
  case class MultiClosure(metas: Seq[Abstract], term: Abstract) extends ClosureT {
    def diff(depth: Int, x: Int): MultiClosure = MultiClosure(metas.map(_.diff(depth + 1, x)), term.diff(depth + 1, x))
  }
  case class MetaEnclosed(metas: Seq[Abstract], term: Abstract) extends MetaEnclosedT {
    def diff(depth: Int, x: Int): MetaEnclosed = MetaEnclosed(metas.map(_.diff(depth + 1, x)), term.diff(depth + 1, x))
  }


  type ClosureGraph = Seq[(Seq[Int], MetaEnclosed)]

  case class Universe(i: Int) extends Abstract

  case class Reference(up: Int, index: Int) extends Abstract

  case class MetaReference(up: Int, index: Int) extends Abstract

  case class Function(domain: Abstract, impict: Boolean, codomain: Closure) extends Abstract

  case class Lambda(closure: Closure) extends Abstract

  case class App(left: Abstract, right: Abstract) extends Abstract

  case class Record(level: Int, names: Seq[Name], implicits: Seq[Boolean], graph: ClosureGraph) extends Abstract

  case class Projection(left: Abstract, field: Int) extends Abstract

  case class Constructor(name: Name, implicits: Seq[Boolean], params: ClosureGraph)

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

  case class Restricted(term: Abstract, restriction: Seq[DimensionPair]) extends Abstract

  // restriction doesn't take binding, but they have a level non-the-less
  case class Face(pair: DimensionPair, body: AbsClosure) {
    def diff(depth: Int, x: Int): Face = Face(pair.diff(depth, x), body.diff(depth, x))

    def dependencies(i: Int): Set[Dependency] = body.dependencies(i + 1)
  }

  case class DimensionPair(from: Dimension, to: Dimension) {
    def diff(depth: Int, x: Int): DimensionPair = DimensionPair(from.diff(depth, x), to.diff(depth, x))

  }

  sealed trait Dimension {
    def diff(depth: Int, x: Int): Abstract.Dimension = {
      this match {
        case Dimension.Reference(up) =>
          if (up > depth) {
            Dimension.Reference(up + x)
          } else {
            this
          }
        case Dimension.Restricted(a, restriction) =>
          Dimension.Restricted(a.diff(depth, x), restriction.map(_.diff(depth, x)))
        case _ => this
      }
    }

  }

  object Dimension {
    case class Reference(up: Int) extends Dimension
    case object True extends Dimension
    case object False extends Dimension
    case class Restricted(a: Dimension, restriction: Seq[DimensionPair]) extends Dimension
  }
}
