package mlang.concrete

import mlang.name._


sealed trait Term {
}

case class NameType(names: Seq[(Boolean, Name)], ty: Term)

object NameType {
  type Flat = (Boolean, Name, Term)
  type FlatSeq = Seq[Flat]

  def flatten(names: Seq[NameType]): NameType.FlatSeq = names.flatMap(n => {
    if (n.names.isEmpty) {
      Seq((false, Name.empty, n.ty))
    } else {
      n.names.map(m => (m._1, m._2, n.ty))
    }
  })
}

sealed trait Block

object Term {

  case class Universe(level: Int) extends Term
  case class Up(a: Reference, i: Int) extends Term

  case class Reference(name: Ref) extends Term // some name is renamed

  case class Cast(term: Term, typ: Term) extends Term

  case class Function(domain: Seq[NameType], codomain: Term) extends Term

  case class Record(fields: Seq[NameType]) extends Term {
    val names = fields.flatMap(_.names)
  }

  case class Constructor(name: Name, term: Seq[NameType])
  case class Sum(constructors: Seq[Constructor]) extends Term with Block

  case class App(left: Term, right: Seq[(Boolean, Term)]) extends Term

  case class Projection(left: Term, right: Ref) extends Term


  case class Case(pattern: Pattern, body: Term)
  case class PatternLambda(implt: Boolean, branches: Seq[Case]) extends Term
  case class Lambda(name: Name, imps: Boolean, body: Term) extends Term

  // TODO can you define a macro in a abstracted context?
  case class Let(declarations: Seq[Declaration], in: Term) extends Term with Block

  // TODO case class Object() big syntax with define and stuff
  // TODO make expression, type is inferred as non-dependent

  case object I extends Term
  case class PathType(typ: Option[Term], left: Term, right: Term) extends Term
  case class ConstantDimension(isOne: Boolean) extends Term

  case class Pair(from: Term, to: Term)
  case class Face(dimension: Pair, term: Term)
  case class Coe(direction: Pair, typ: Term, base: Term) extends Term
  case class Hcom(direction: Pair, base: Term, ident: Name, faces: Seq[Face]) extends Term
  case class Com(direction: Pair, typ: Term, base: Term, ident: Name, faces: Seq[Face]) extends Term

  case object Hole extends Term
}

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
  sealed trait InvocationForm
  object InvocationForm {
    case class Reference(name: Name) extends InvocationForm
    case class ConstProjection(ref: Ref, name: Name) extends InvocationForm
    case class Projection(tele: Seq[NameType], name: Name) extends InvocationForm
  }

  case class Define(modifiers: Seq[Modifier], from: InvocationForm, parameters: Seq[NameType], typ: Option[Term], term: Term) extends Declaration
  // depending on our algorithm, recursive ones might not need to declare first
  case class Declare(modifiers: Seq[Modifier], from: InvocationForm, parameters: Seq[NameType], typ: Term) extends Declaration
}





sealed trait Pattern

object Pattern {
  case class Atom(id: Name) extends Pattern
  case class Group(names: Seq[Pattern]) extends Pattern
  // TODO user defined named patterns
  case class NamedGroup(name: Ref, pattern: Seq[Pattern]) extends Pattern
}
