package mlang.compiler.dbi

import mlang.utils._
import mlang.compiler.Pattern


sealed trait DependencyType
object DependencyType {
  case object Value extends DependencyType
  case object Meta extends DependencyType
  case object Formula extends DependencyType
}

case class Dependency(x: Int, i: Int, typ: DependencyType) {
  def diff(j: Int): Dependency = Dependency(x + j, i, typ)
}

trait Dbi[T] {
  def (t: T) dependencies(depth: Int): Set[Dependency]
  def (t: T) diff(depth: Int, x: Int): T
  def (t: T) dependencies: Set[Dependency] = t.dependencies(0)
  def (t: T) diff(x: Int): T = t.diff(0, x)
}

sealed trait Formula
object Formula {
  case class Reference(up: Int, index: Int) extends Formula
  case object True extends Formula
  case object False extends Formula
  case class And(left: Formula, right: Formula) extends Formula
  case class Or(left: Formula, right: Formula) extends Formula
  case class Neg(unit: Formula) extends Formula
}
given Dbi[Formula] {
    import Formula._
    def (f: Formula) dependencies(depth: Int): Set[Dependency] = f match {
      case Reference(up, i) => if (up >= depth) Set(Dependency(up - depth, i, DependencyType.Formula)) else Set.empty
      case And(l, r) => l.dependencies(depth) ++ r.dependencies(depth)
      case Or(l, r) => l.dependencies(depth) ++ r.dependencies(depth)
      case Neg(l) => l.dependencies(depth)
      case _ => Set.empty
    }

    def (f: Formula) diff(depth: Int, x: Int): Formula = f match {
      case Reference(up, i) => if (up >= depth) Reference(up + x, i) else  f
      case And(l, r) => And(l.diff(depth, x), r.diff(depth, x))
      case Or(l, r) => Or(l.diff(depth, x), r.diff(depth, x))
      case Neg(l) => Neg(l.diff(depth, x))
      case _ => f
    }
}

case class Closure(metas: Seq[Abstract], term: Abstract)
given Dbi[Closure] {
  def (m: Closure) dependencies(i: Int): Set[Dependency] = m.metas.flatMap(_.dependencies(i + 1)).toSet ++ m.term.dependencies(i + 1)
  def (m: Closure) diff(depth: Int, x: Int): Closure = Closure(m.metas.map(_.diff(depth + 1, x)), m.term.diff(depth + 1, x))
}

type System = Map[Formula, Closure]
given Dbi[System] {
  def (s: System) diff(depth: Int, x: Int): System =
    s.map(a => (a._1.diff(depth, x), a._2.diff(depth + 1, x)))
  def (s: System) dependencies(i: Int): Set[Dependency] = s.flatMap(a => a._1.dependencies(i) ++ a._2.dependencies(i + 1)).toSet
}


object ClosureGraph {
  case class Node(implicitt: Boolean, deps: Seq[Int], typ: Closure)
}
case class ClosureGraph(nodes:Seq[ClosureGraph.Node], dims: Int = 0, restrictions: System = Map.empty)
given Dbi[ClosureGraph.Node] {
    def (n: ClosureGraph.Node) diff(depth: Int, x: Int): ClosureGraph.Node = ClosureGraph.Node(n.implicitt, n.deps, n.typ.diff(depth, x))
    def (n: ClosureGraph.Node) dependencies(i: Int): Set[Dependency]  = n.typ.dependencies(i)
}
object ClosureGraphRestrictionSystemDbi {
  def diff(s: System, depth: Int, x: Int): System =
    s.map(a => (a._1.diff(depth, x), a._2.diff(depth, x)))
  def dependencies(s: System, i: Int): Set[Dependency] = s.flatMap(a => a._1.dependencies(i) ++ a._2.dependencies(i)).toSet
}
given Dbi[ClosureGraph] {
  def (g: ClosureGraph) dependencies(i: Int): Set[Dependency]  = g.nodes.flatMap(_.dependencies(i)).toSet ++ ClosureGraphRestrictionSystemDbi.dependencies(g.restrictions, i + 1)
  def (g: ClosureGraph) diff(depth: Int, x: Int): ClosureGraph = ClosureGraph(g.nodes.map(_.diff(depth, x)), g.dims, ClosureGraphRestrictionSystemDbi.diff(g.restrictions, depth + 1, x))
}

  // LATER this is just a marker, we might have Record(recursive: Option[RecursiveType], ...) later
sealed trait Recursively
case class Inductively(id: Long, typ: Abstract, ps: Seq[Abstract]) extends Recursively

// this restriction multi closure system lives 1 level bellow
case class Constructor(name: Name, params: ClosureGraph)
case class Case(pattern: Pattern, body: Closure)

sealed trait Abstract
object Abstract {
  case class Universe(i: Int) extends Abstract

  case class Reference(up: Int, index: Int) extends Abstract
  case class MetaReference(up: Int, index: Int) extends Abstract
  case class Let(metas: Seq[Abstract], definitions: Seq[Abstract], in: Abstract) extends Abstract

  case class Function(domain: Abstract, impict: Boolean, codomain: Closure) extends Abstract
  case class Lambda(closure: Closure) extends Abstract
  case class PatternLambda(id: Long, domain: Abstract, typ: Closure, cases: Seq[Case]) extends Abstract
  case class App(left: Abstract, right: Abstract) extends Abstract


  case class Record(inductively: Option[Inductively], names: Seq[Name], graph: ClosureGraph) extends Abstract
  case class Projection(left: Abstract, field: Int) extends Abstract
  case class Make(vs: Seq[Abstract]) extends Abstract

  case class Sum(inductively: Option[Inductively], hit: Boolean, constructors: Seq[Constructor]) extends Abstract {
    override def toString = s"SUM(${constructors.map(_.name)})"
  }
  case class Construct(f: Int, vs: Seq[Abstract], ds: Seq[Formula], ty: System) extends Abstract

  case class PathLambda(body: Closure) extends Abstract
  case class PathType(typ: Closure, left: Abstract, right: Abstract) extends Abstract
  case class PathApp(let: Abstract, r: Formula) extends Abstract

  case class Transp(tp: Closure, direction: Formula, base: Abstract) extends Abstract
  case class Hcomp(tp: Abstract, base: Abstract, faces: System) extends Abstract

  case class Comp(tp: Closure, base: Abstract, faces: System) extends Abstract

  case class GlueType(tp: Abstract, faces: System) extends Abstract
  case class Glue(base: Abstract, faces: System) extends Abstract
  case class Unglue(tp: Abstract, base: Abstract, iu: Boolean, faces: System) extends Abstract
}

given Dbi[Inductively] {
    def (d: Inductively) dependencies(depth: Int): Set[Dependency] = d.typ.dependencies(depth) ++ d.ps.flatMap(_.dependencies(depth))
    def (d: Inductively) diff(depth: Int, x: Int): Inductively = Inductively(d.id, d.typ.diff(depth, x), d.ps.map(_.diff(depth, x)))
}

given Dbi[Constructor] {
    def (c: Constructor) dependencies(depth: Int): Set[Dependency] = c.params.dependencies(depth)
    def (c: Constructor) diff(depth: Int, x: Int): Constructor = Constructor(c.name, c.params.diff(depth, x))
}

given Dbi[Abstract] {

  import Abstract._

  def (a: Abstract) diff(depth: Int, x: Int): Abstract = a match {
    case _: Universe => a
    case Reference(up, index) =>
      if (up >= depth) Reference(up + x, index) else a
    case MetaReference(up, index) =>
      if (up >= depth) MetaReference(up + x, index) else a
    case Let(metas, definitions, in) => Let(metas.map(_.diff(depth + 1, x)), definitions.map(_.diff(depth + 1, x)), in.diff(depth + 1, x))
    case Function(domain, impict, codomain) => Function(domain.diff(depth, x), impict, codomain.diff(depth, x))
    case Lambda(closure) => Lambda(closure.diff(depth, x))
    case App(left, right) => App(left.diff(depth, x), right.diff(depth, x))
    case Record(id, names, graph) => Record(id.map(_.diff(depth, x)), names, graph.diff(depth, x))
    case Projection(left, field) => Projection(left.diff(depth, x), field)
    case Sum(id, hit, constructors) => Sum(id.map(_.diff(depth, x)), hit, constructors.map(_.diff(depth, x)))
    case Make(vs) => Make(vs.map(_.diff(depth, x)))
    case Construct(f, vs, fs, ty) => Construct(f, vs.map(_.diff(depth, x)), fs.map(_.diff(depth, x)), ty.diff(depth, x))
    case PatternLambda(id, dom, typ, cases) => PatternLambda(id, dom.diff(depth, x), typ.diff(depth, x), cases.map(a => Case(a.pattern, a.body.diff(depth, x))))
    case PathLambda(body) => PathLambda(body.diff(depth, x))
    case PathType(typ, left, right) => PathType(typ.diff(depth, x), left.diff(depth, x), right.diff(depth, x))
    case PathApp(let, r) => PathApp(let.diff(depth, x), r.diff(depth, x))
    case Transp(tp, direction, base) => Transp(tp.diff(depth, x), direction.diff(depth, x), base.diff(depth, x))
    case Hcomp(tp, base, faces) => Hcomp(tp.diff(depth, x), base.diff(depth, x), faces.diff(depth, x))
    case Comp(tp, base, faces) => Comp(tp.diff(depth, x), base.diff(depth, x), faces.diff(depth, x))
    case GlueType(tp, faces) => GlueType(tp.diff(depth, x), faces.diff(depth, x))
    case Glue(tp, faces) => Glue(tp.diff(depth, x), faces.diff(depth, x))
    case Unglue(tp, base, iu, faces) => Unglue(tp.diff(depth, x), base.diff(depth, x), iu, faces.diff(depth, x))
  }

  def (a: Abstract) dependencies(i: Int): Set[Dependency] = a match {
    case Reference(up, index) =>
      // println(s"$i $up $index")
       if (up >= i) Set(Dependency(up - i, index, DependencyType.Value)) else Set.empty
    case MetaReference(up, index) => if (up >= i) Set(Dependency(up - i, index, DependencyType.Meta)) else Set.empty
    case Let(metas, definitions, in) =>
      metas.flatMap(a => a.dependencies(i + 1)).toSet ++ definitions.flatMap(a => a.dependencies(i + 1)).toSet ++ in.dependencies(i + 1)
    case Universe(_) => Set.empty
    case Function(domain, _, codomain) => domain.dependencies(i) ++ codomain.dependencies(i)
    case Lambda(closure) => closure.dependencies(i)
    case App(left, right) => left.dependencies(i) ++ right.dependencies(i)
    case Record(id, _, nodes) => id.map(_.dependencies(i)).getOrElse(Set.empty) ++ nodes.dependencies(i)
    case Projection(left, _) => left.dependencies(i)
    case Sum(id, hit, constructors) =>  id.map(_.dependencies(i)).getOrElse(Set.empty) ++ constructors.flatMap(_.dependencies(i)).toSet
    case Make(vs) => vs.flatMap(_.dependencies(i)).toSet
    case Construct(_, vs, fs, ty) => vs.flatMap(_.dependencies(i)).toSet ++ fs.flatMap(_.dependencies(i)) ++ ty.dependencies(i)
    case PatternLambda(_, dom, cd, cases) => dom.dependencies(i) ++ cd.dependencies(i) ++ cases.flatMap(_.body.dependencies(i)).toSet
    case PathLambda(body) => body.dependencies(i)
    case PathType(typ, left, right) => typ.dependencies(i) ++ left.dependencies(i) ++ right.dependencies(i)
    case PathApp(lef, right) => lef.dependencies(i) ++ right.dependencies(i)
    case Transp(tp, dir, base) => tp.dependencies(i) ++ dir.dependencies(i) ++ base.dependencies(i)
    case Hcomp(tp, base, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ faces.dependencies(i)
    case Comp(tp, base, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ faces.dependencies(i)
    case GlueType(tp, faces) => tp.dependencies(i)  ++ faces.dependencies(i)
    case Glue(base, faces) => base.dependencies(i) ++ faces.dependencies(i)
    case Unglue(tp, base, iu, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ faces.dependencies(i)
  }
}