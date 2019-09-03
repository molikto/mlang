package mlang.compiler

import mlang.utils.{Name, Text}

sealed trait Concrete

object Concrete {

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
    case class Group(names: Seq[Pattern]) extends Pattern
    // TODO user defined named patterns
    case class NamedGroup(name: Text, pattern: Seq[Pattern]) extends Pattern
  }



  case object Type extends Concrete
  case object I extends Concrete
  case object True extends Concrete
  case object False extends Concrete
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

  case class Constructor(name: Name, term: Seq[NameType])

  case class Sum(constructors: Seq[Constructor]) extends Concrete

  case class App(left: Concrete, right: Seq[(Boolean, Concrete)]) extends Concrete

  case class Projection(left: Concrete, right: Concrete) extends Concrete

  case class Case(pattern: Pattern, body: Concrete)

  case class PatternLambda(implt: Boolean, branches: Seq[Case]) extends Concrete

  case class Lambda(name: Name, imps: Boolean, body: Concrete) extends Concrete

  // TODO can you define a macro in a abstracted context?
  case class Let(declarations: Seq[Declaration], in: Concrete) extends Concrete
  // TODO make expression, type is inferred as non-dependent
  case class PathType(typ: Option[Concrete], left: Concrete, right: Concrete) extends Concrete
  case class Face(dimension: Concrete, term: Concrete)
  case class Coe(direction: Concrete, typ: Concrete, base: Concrete) extends Concrete
  case class Hcom(direction: Concrete, base: Concrete, faces: Seq[Face]) extends Concrete
  case class Com(direction: Concrete, typ: Concrete, base: Concrete, faces: Seq[Face]) extends Concrete
  case class VType(x: Concrete, a: Concrete, b: Concrete, e: Concrete) extends Concrete
  case class VMake(m: Concrete, n: Concrete) extends Concrete
  case class VProj(m: Concrete) extends Concrete

  case object Undefined extends Concrete
  case object Hole extends Concrete


  case class Module(declarations: Seq[Declaration])




  sealed trait Declaration {
    def modifiers: Seq[Declaration.Modifier]
  }

  object Declaration {
    sealed trait Modifier
    object Modifier {
      case object WithConstructor extends Modifier
      case object Inductively extends Modifier
      case object __Debug extends Modifier
    }

    case class Define(modifiers: Seq[Modifier], name: Name, parameters: Seq[NameType], typ: Option[Concrete], term: Concrete) extends Declaration
    // depending on our algorithm, recursive ones might not need to declare first
    case class Declare(modifiers: Seq[Modifier], name: Name, parameters: Seq[NameType], typ: Concrete) extends Declaration
  }

}






