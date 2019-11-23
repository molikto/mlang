package mlang.compiler.concrete

import mlang.utils.{Name, Text}

sealed trait Concrete


case class NameType(names: Seq[(Boolean, Name)], ty: Concrete)

object NameType {
  type Flat = (Boolean, Name, Concrete)
  type FlatSeq = Seq[Flat]

  def flatten(names: Seq[NameType]): NameType.FlatSeq = names.flatMap(n => {
    if (n.names.isEmpty) {
      Seq((false, Name.empty, n.ty))
    } else {
      n.names.map(m => (m._1, m._2, n.ty))
    }
  })
}

sealed trait Pattern

object Pattern {
  case class Atom(id: Name) extends Pattern
  case class Group(names: Seq[(Boolean, Pattern)]) extends Pattern
  // TODO user defined named patterns
  case class NamedGroup(name: Text, pattern: Seq[(Boolean, Pattern)]) extends Pattern
}

case class Face(dimension: Concrete, term: Concrete)
case class Constructor(name: Name, term: Seq[NameType], restrictions: Seq[Face])
case class Case(pattern: Pattern, body: Concrete)

case class Module(declarations: Seq[Declaration])


sealed trait DeclarationModifier
object DeclarationModifier {
  case object WithConstructor extends DeclarationModifier
  case object Inductively extends DeclarationModifier
  case object __Debug extends DeclarationModifier
  case object WithoutDefine extends DeclarationModifier
}

sealed trait Declaration

object Declaration {

  sealed trait Single extends Declaration  {
    def modifiers: Seq[DeclarationModifier]
    def name: Name
  }
  case class Define(modifiers: Seq[DeclarationModifier], name: Name, parameters: Seq[NameType], typ: Option[Concrete], term: Concrete) extends Single
  // depending on our algorithm, recursive ones might not need to declare first
  case class Declare(modifiers: Seq[DeclarationModifier], name: Name, parameters: Seq[NameType], typ: Concrete) extends Single

  // FIXME(SYNTAX) this is kind of wired now, it only generalize the parameters but not the applications
  case class Parameters(parameters: Seq[NameType], items: Seq[Declaration]) extends Declaration
}

object Concrete {

  case object Type extends Concrete
  case object I extends Concrete
  case class Number(str: String) extends Concrete
  case class And(left: Concrete, right: Concrete) extends Concrete
  case class Or(left: Concrete, right: Concrete) extends Concrete
  case class Neg(a: Concrete) extends Concrete

  case object Make extends Concrete // special identifier for maker of a record type

  case class Up(a: Concrete, i: Int) extends Concrete

  case class Reference(name: Text) extends Concrete // some name is renamed

  case class Cast(term: Concrete, typ: Concrete) extends Concrete

  case class Function(domain: Seq[NameType], codomain: Concrete) extends Concrete

  case class Record(fields: Seq[NameType]) extends Concrete {
    val names = fields.flatMap(_.names)
  }


  case class Sum(contextural: Boolean, constructors: Seq[Constructor]) extends Concrete

  case class App(left: Concrete, right: Seq[(Boolean, Concrete)]) extends Concrete
  object App {
    def apply(left: Concrete, right: Concrete): Concrete = App(left, Seq((false, right)))
  }

  case class Projection(left: Concrete, right: Concrete) extends Concrete

  case class PatternLambda(implt: Boolean, branches: Seq[Case]) extends Concrete

  case class Lambda(name: Name, imps: Boolean, ensuredPath: Boolean, body: Concrete) extends Concrete

  // TODO can you define a macro in a abstracted context?
  case class Let(declarations: Seq[Declaration], in: Concrete) extends Concrete
  case class PathType(typ: Option[Concrete], left: Concrete, right: Concrete) extends Concrete
  case class Transp(typ: Concrete, direction: Concrete, base: Concrete) extends Concrete
  case class Hcomp(base: Concrete, faces: Seq[Face]) extends Concrete
  case class Comp(typ: Concrete, base: Concrete, faces: Seq[Face]) extends Concrete
  case class GlueType(x: Concrete, faces: Seq[Face]) extends Concrete
  case class Glue(m: Concrete, faces: Seq[Face]) extends Concrete
  case class Unglue(m: Concrete) extends Concrete

  case object Undefined extends Concrete
  case object Hole extends Concrete
}






