package mlang.compiler

import mlang.compiler.Value.ValueSystem
import mlang.utils.Name

case class Dependency(i: Int, meta: Boolean)

object Abstract {

  /**
   * FORMULA
   */
  object Formula {
    case class Reference(up: Int, index: Int) extends Formula
    case object True extends Formula
    case object False extends Formula
    case class And(left: Formula, right: Formula) extends Formula
    case class Or(left: Formula, right: Formula) extends Formula
    case class Neg(unit: Formula) extends Formula
  }

  sealed trait Formula {
    import Formula.{And, Or, Neg}

    def dependencies(i: Int): Set[Dependency] = Set.empty
    def diff(depth: Int, x: Int): Formula = {
      this match {
        case Formula.Reference(up, i) =>
          if (up > depth) {
            Formula.Reference(up + x, i)
          } else {
            this
          }
        case And(l, r) => And(l.diff(depth, x), r.diff(depth, x))
        case Or(l, r) => Or(l.diff(depth, x), r.diff(depth, x))
        case Neg(l) => Neg(l.diff(depth, x))
        case _ => this
      }
    }

  }

  /**
   * CLOSURES
   */
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

  case class ClosureGraph(nodes:Seq[ClosureGraph.Node], dims: Int = 0, restrictions: EnclosedSystem = Map.empty) {
    def dependencies(i: Int) = nodes.flatMap(_.dependencies(i)).toSet ++ EnclosedSystem.dependencies(restrictions, i + 1)
    def diff(depth: Int, x: Int): ClosureGraph = ClosureGraph(nodes.map(_.diff(depth, x)), dims, EnclosedSystem.diff(restrictions, depth + 1, x))
  }
  object ClosureGraph {
    case class Node(implicitt: Boolean, deps: Seq[Int], typ: MetaEnclosed) {
      def diff(depth: Int, x: Int) = Node(implicitt, deps, typ.diff(depth, x))
      def dependencies(i: Int) = typ.dependencies(i)
    }
  }

  /**
   * ABSTRACT
   */

  case class Universe(i: Int) extends Abstract

  case class Reference(up: Int, index: Int) extends Abstract
  case class MetaReference(up: Int, index: Int) extends Abstract
  case class Let(metas: Seq[Abstract], definitions: Seq[Abstract], in: Abstract) extends Abstract

  case class Function(domain: Abstract, impict: Boolean, codomain: Closure) extends Abstract
  case class Lambda(closure: Closure) extends Abstract
  case class PatternLambda(id: Long, domain: Abstract, typ: Closure, cases: Seq[Case]) extends Abstract
  case class App(left: Abstract, right: Abstract) extends Abstract

  // LATER this is just a marker, we might have Record(recursive: Option[RecursiveType], ...) later
  sealed trait RecursiveType
  case class Inductively(id: Long, typ: Abstract, ps: Seq[Abstract]
                       /*  , parameters: Seq[Abstract], parameterTypes: ClosureGraph */
                        ) extends RecursiveType {
    def dependencies(i: Int): Set[Dependency] = typ.dependencies(i) ++ ps.flatMap(_.dependencies(i))
    def diff(depth: Int, x: Int): Inductively = Inductively(id, typ.diff(depth, x), ps.map(_.diff(depth, x)))
    override def toString: String = "inductively"
  }

  case class Record(inductively: Option[Inductively], names: Seq[Name], graph: ClosureGraph) extends Abstract
  case class Projection(left: Abstract, field: Int) extends Abstract
  case class Make(vs: Seq[Abstract]) extends Abstract

  // this restriction multi closure system lives 1 level bellow
  case class Constructor(name: Name, params: ClosureGraph) {
    def dependencies(i: Int): Set[Dependency] = params.dependencies(i)
    def diff(depth: Int, x: Int): Constructor = Constructor(name, params.diff(depth, x))
  }
  case class Sum(inductively: Option[Inductively], hit: Boolean, constructors: Seq[Constructor]) extends Abstract
  case class Case(pattern: Pattern, body: MultiClosure)
  case class Construct(f: Int, vs: Seq[Abstract], ds: Seq[Abstract.Formula], ty: EnclosedSystem) extends Abstract

  case class PathLambda(body: AbsClosure) extends Abstract
  case class PathType(typ: AbsClosure, left: Abstract, right: Abstract) extends Abstract
  case class PathApp(let: Abstract, r: Formula) extends Abstract

  // restriction doesn't take binding, but they have a level non-the-less
  type System[T] = Map[Formula, T]
  type AbsClosureSystem = System[AbsClosure]
  object AbsClosureSystem {
    def diff(s: AbsClosureSystem, depth: Int, x: Int): AbsClosureSystem =
      s.map(a => (a._1.diff(depth, x), a._2.diff(depth, x)))
    def dependencies(s: AbsClosureSystem, i: Int): Set[Dependency] = s.values.flatten(_.dependencies(i)).toSet
  }
  type EnclosedSystem = System[MetaEnclosed]
  object EnclosedSystem {
    // TODO copied code, same in value
    def diff(s: EnclosedSystem, depth: Int, x: Int): EnclosedSystem =
      s.map(a => (a._1.diff(depth, x), a._2.diff(depth, x)))
    def dependencies(s: EnclosedSystem, i: Int): Set[Dependency] = s.values.flatten(_.dependencies(i)).toSet

    val empty: EnclosedSystem = Map.empty

  }

  type MultiClosureSystem = System[MultiClosure]
  object MultiClosureSystem {
    // TODO copied code, same in value
    def diff(s: MultiClosureSystem, depth: Int, x: Int): MultiClosureSystem =
      s.map(a => (a._1.diff(depth, x), a._2.diff(depth, x)))
    def dependencies(s: MultiClosureSystem, i: Int): Set[Dependency] = s.values.flatten(_.dependencies(i)).toSet
  }

  case class Transp(tp: AbsClosure, direction: Formula, base: Abstract) extends Abstract
  case class Hcomp(tp: Abstract, base: Abstract, faces: AbsClosureSystem) extends Abstract

  case class Comp(tp: AbsClosure, base: Abstract, faces: AbsClosureSystem) extends Abstract

  case class GlueType(tp: Abstract, faces: EnclosedSystem) extends Abstract
  case class Glue(base: Abstract, faces: EnclosedSystem) extends Abstract
  case class Unglue(tp: Abstract, base: Abstract, iu: Boolean, faces: EnclosedSystem) extends Abstract
}


sealed trait Abstract {
  import Abstract._

  def termDependencies(i: Int): Set[Int] = dependencies(i).flatMap {
    case Dependency(i, false) => Set(i)
    case _ => Set.empty[Int]
  }

  def diff(depth: Int, x: Int): Abstract = this match {
    case _: Universe => this
    case Reference(up, index) =>
      if (up >= depth) {
        assert(up + x >= 0)
        Reference(up + x, index)
      } else {
        this
      }
    case MetaReference(up, index) =>
      if (up >= depth) {
        MetaReference(up + x, index)
      } else {
        this
      }
    case Function(domain, impict, codomain) =>
      Function(domain.diff(depth, x), impict, codomain.diff(depth, x))
    case Lambda(closure) => Lambda(closure.diff(depth, x))
    case App(left, right) => App(left.diff(depth, x), right.diff(depth, x))
    case Record(id, names, graph) => Record(id.map(_.diff(depth, x)), names, graph.diff(depth, x))
    case Projection(left, field) => Projection(left.diff(depth, x), field)
    case Sum(id, hit, constructors) => Sum(id.map(_.diff(depth, x)), hit, constructors.map(_.diff(depth, x)))
    case Make(vs) => Make(vs.map(_.diff(depth, x)))
    case Construct(f, vs, fs, ty) => Construct(f, vs.map(_.diff(depth, x)), fs.map(_.diff(depth, x)), EnclosedSystem.diff(ty, depth, x))
    case Let(metas, definitions, in) => Let(metas.map(_.diff(depth + 1, x)), definitions.map(_.diff(depth + 1, x)), in.diff(depth + 1, x))
    case PatternLambda(id, dom, typ, cases) => PatternLambda(id, dom.diff(depth, x), typ.diff(depth, x), cases.map(a => Case(a.pattern, a.body.diff(depth, x))))
    case PathLambda(body) => PathLambda(body.diff(depth, x))
    case PathType(typ, left, right) => PathType(typ.diff(depth, x), left.diff(depth, x), right.diff(depth, x))
    case PathApp(let, r) => PathApp(let.diff(depth, x), r.diff(depth, x))
    case Transp(tp, direction, base) => Transp(tp.diff(depth, x), direction.diff(depth, x), base.diff(depth, x))
    case Hcomp(tp, base, faces) => Hcomp(tp.diff(depth, x), base.diff(depth, x), AbsClosureSystem.diff(faces, depth, x))
    case Comp(tp, base, faces) => Comp(tp.diff(depth, x), base.diff(depth, x), AbsClosureSystem.diff(faces, depth, x))
    case GlueType(tp, faces) => GlueType(tp.diff(depth, x), EnclosedSystem.diff(faces, depth, x))
    case Glue(tp, faces) => Glue(tp.diff(depth, x), EnclosedSystem.diff(faces, depth, x))
    case Unglue(tp, base, iu, faces) => Unglue(tp.diff(depth, x), base.diff(depth, x), iu, EnclosedSystem.diff(faces, depth, x))
  }

  def dependencies(i: Int): Set[Dependency] = this match {
    case Universe(_) => Set.empty
    //case Reference(up, index) => if (i == up) Set(index) else Set.empty
    //case MetaReference(up, index) => Set.empty
    case Reference(up, index) => if (i == up) Set(Dependency(index, meta = false)) else Set.empty
    case MetaReference(up, index) => if (i == up) Set(Dependency(index, meta = true)) else Set.empty
    case Function(domain, _, codomain) => domain.dependencies(i) ++ codomain.dependencies(i)
    case Lambda(closure) => closure.dependencies(i)
    case App(left, right) => left.dependencies(i) ++ right.dependencies(i)
    case Record(id, _, nodes) => id.map(_.dependencies(i)).getOrElse(Set.empty) ++ nodes.dependencies(i)
    case Projection(left, _) => left.dependencies(i)
    case Sum(id, hit, constructors) =>  id.map(_.dependencies(i)).getOrElse(Set.empty) ++ constructors.flatMap(_.dependencies(i)).toSet
    case Make(vs) => vs.flatMap(_.dependencies(i)).toSet
    case Construct(_, vs, fs, ty) => vs.flatMap(_.dependencies(i)).toSet ++ EnclosedSystem.dependencies(ty, i)
    case Let(metas, definitions, in) =>
      metas.flatMap(a => a.dependencies(i + 1)).toSet  ++ definitions.flatMap(a => a.dependencies(i + 1)).toSet ++ in.dependencies(i + 1)
    case PatternLambda(_, dom, cd, cases) => dom.dependencies(i) ++ cd.dependencies(i) ++ cases.flatMap(_.body.dependencies(i)).toSet
    case PathLambda(body) => body.dependencies(i)
    case PathType(typ, left, right) => typ.dependencies(i) ++ left.dependencies(i) ++ right.dependencies(i)
    case PathApp(lef, _) => lef.dependencies(i)
    case Transp(tp, _, base) => tp.dependencies(i) ++ base.dependencies(i)
    case Hcomp(tp, base, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ AbsClosureSystem.dependencies(faces, i)
    case Comp(tp, base, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ AbsClosureSystem.dependencies(faces, i)
    case GlueType(tp, faces) => tp.dependencies(i)  ++ EnclosedSystem.dependencies(faces, i)
    case Glue(base, faces) => base.dependencies(i) ++ EnclosedSystem.dependencies(faces, i)
    case Unglue(tp, base, iu, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ EnclosedSystem.dependencies(faces, i)
  }
}

