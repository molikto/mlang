package mlang.compiler

import mlang.utils.Name

case class Dependency(i: Int, meta: Boolean)

object Abstract {

  /**
   * FORMULA
   */
  object Formula {
    case class Reference(up: Int) extends Formula
    case object True extends Formula
    case object False extends Formula
    case class And(left: Formula, right: Formula) extends Formula
    case class Or(left: Formula, right: Formula) extends Formula
    case class Neg(unit: Formula) extends Formula
  }

  sealed trait Formula {
    import Formula.{And, Or, Neg}

    def diff(depth: Int, x: Int): Formula = {
      this match {
        case Formula.Reference(up) =>
          if (up > depth) {
            Formula.Reference(up + x)
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

  type ClosureGraph = Seq[(Seq[Int], MetaEnclosed)]

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

  case class Inductively(id: Long, level: Int) {
    def dependencies(i: Int): Set[Dependency] = Set.empty
    def diff(depth: Int, x: Int): Inductively = this
  }
  case class Maker(sum: Abstract, field: Int) extends Abstract

  case class Record(inductively: Option[Inductively], names: Seq[Name], implicits: Seq[Boolean], graph: ClosureGraph) extends Abstract
  case class Projection(left: Abstract, field: Int) extends Abstract

  case class Constructor(name: Name, implicits: Seq[Boolean], params: ClosureGraph)
  case class Sum(inductively: Option[Inductively], constructors: Seq[Constructor]) extends Abstract
  case class Case(pattern: Pattern, body: MultiClosure)

  case class PathLambda(body: AbsClosure) extends Abstract
  case class PathType(typ: AbsClosure, left: Abstract, right: Abstract) extends Abstract
  case class PathApp(let: Abstract, r: Formula) extends Abstract

  // restriction doesn't take binding, but they have a level non-the-less
  type System[T] = Map[Formula, T]
  case class Face(pair: Formula, body: AbsClosure) {
    def diff(depth: Int, x: Int): Face = Face(pair.diff(depth, x), body.diff(depth + 1, x))
    def dependencies(i: Int): Set[Dependency] = body.dependencies(i + 1)
  }

  object Face {
    def diff(faces: Seq[Face], depth: Int, x: Int): Seq[Face] = faces.map(_.diff(depth, x))

    def dependencies(faces: Seq[Face], i: Int): IterableOnce[Dependency] = faces.flatMap(_.dependencies(i)).toSet 
  }

  case class Transp(tp: AbsClosure, direction: Formula, base: Abstract) extends Abstract
  case class Hcom(tp: Abstract, base: Abstract, faces: Seq[Face]) extends Abstract

  case class Com(tp: AbsClosure, base: Abstract, faces: Seq[Face]) extends Abstract

  // FIXME don't use face anymore!!! it is wrong concept!!
  case class GlueType(tp: Abstract, faces: Seq[Face]) extends Abstract
  case class Glue(base: Abstract, faces: Seq[Face]) extends Abstract
  case class Unglue(tp: Abstract, base: Abstract, faces: Seq[Face]) extends Abstract
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
    case Record(id, names, implicits, graph) => Record(id.map(_.diff(depth, x)), names, implicits, graph.map(a => (a._1, a._2.diff(depth, x))))
    case Projection(left, field) => Projection(left.diff(depth, x), field)
    case Sum(id, constructors) => Sum(id.map(_.diff(depth, x)), constructors.map(c => Constructor(c.name, c.implicits, c.params.map(a => (a._1, a._2.diff(depth, x))))))
    case Maker(sum, field) => Maker(sum.diff(depth, x), field)
    case Let(metas, definitions, in) => Let(metas.map(_.diff(depth + 1, x)), definitions.map(_.diff(depth + 1, x)), in.diff(depth + 1, x))
    case PatternLambda(id, dom, typ, cases) => PatternLambda(id, dom.diff(depth, x), typ.diff(depth, x), cases.map(a => Case(a.pattern, a.body.diff(depth, x))))
    case PathLambda(body) => PathLambda(body.diff(depth, x))
    case PathType(typ, left, right) => PathType(typ.diff(depth, x), left.diff(depth, x), right.diff(depth, x))
    case PathApp(let, r) => PathApp(let.diff(depth, x), r.diff(depth, x))
    case Transp(tp, direction, base) => Transp(tp.diff(depth, x), direction.diff(depth, x), base.diff(depth, x))
    case Hcom(tp, base, faces) => Hcom(tp.diff(depth, x), base.diff(depth, x), Face.diff(faces, depth, x))
    case Com(tp, base, faces) => Com(tp.diff(depth, x), base.diff(depth, x), Face.diff(faces, depth, x))
    case GlueType(tp, faces) => GlueType(tp.diff(depth, x), Face.diff(faces, depth, x))
    case Glue(tp, faces) => Glue(tp.diff(depth, x), Face.diff(faces, depth, x))
    case Unglue(tp, base, faces) => Unglue(tp.diff(depth, x), base.diff(depth, x), Face.diff(faces, depth, x))
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
    case Record(id, _, _, nodes) => id.map(_.dependencies(i)).getOrElse(Set.empty) ++ nodes.flatMap(_._2.dependencies(i)).toSet
    case Projection(left, _) => left.dependencies(i)
    case Sum(id, constructors) =>  id.map(_.dependencies(i)).getOrElse(Set.empty) ++ constructors.flatMap(_.params.flatMap(_._2.dependencies(i))).toSet
    case Maker(sum, _) => sum.dependencies(i)
    case Let(metas, definitions, in) =>
      metas.flatMap(a => a.dependencies(i + 1)).toSet  ++ definitions.flatMap(a => a.dependencies(i + 1)).toSet ++ in.dependencies(i + 1)
    case PatternLambda(_, dom, cd, cases) => dom.dependencies(i) ++ cd.dependencies(i) ++ cases.flatMap(_.body.dependencies(i)).toSet
    case PathLambda(body) => body.dependencies(i)
    case PathType(typ, left, right) => typ.dependencies(i) ++ left.dependencies(i) ++ right.dependencies(i)
    case PathApp(lef, _) => lef.dependencies(i)
    case Transp(tp, _, base) => tp.dependencies(i) ++ base.dependencies(i)
    case Hcom(tp, base, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ Face.dependencies(faces, i)
    case Com(tp, base, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ Face.dependencies(faces, i)
    case GlueType(tp, faces) => tp.dependencies(i)  ++ Face.dependencies(faces, i)
    case Glue(base, faces) => base.dependencies(i) ++ Face.dependencies(faces, i)
    case Unglue(tp, base, faces) => tp.dependencies(i) ++ base.dependencies(i) ++ Face.dependencies(faces, i)
  }
}

