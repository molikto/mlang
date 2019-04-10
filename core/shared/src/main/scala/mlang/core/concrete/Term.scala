package mlang.core.concrete

sealed trait Term

object Term {
  case class Universe(level: Int) extends Term

  case class Reference(name: NameRef) extends Term // some name is renamed

  case class Cast(term: Term, typ: Term) extends Term

  case class Function(domain: Term, name: Name, codomain: Term) extends Term
  case class Lambda(name: Name, codomain: Term) extends Term
  case class Application(left: Term, right: Term) extends Term

  case class NameType(name: Name, ty: Term)
  case class Record(fields: Seq[NameType]) extends Term
  case class Projection(left: Term, right: NameRef) extends Term

  case class Constructor(name: Name, term: Seq[NameType])
  case class Sum(constructors: Seq[Constructor]) extends Term

  case class Case(pattern: Pattern, body: Term)
  case class PatternLambda(branches: Seq[Case]) extends Term

  // TODO can you define a macro in a abstracted context?
  case class Let(declarations: Seq[Declaration], in: Term) extends Term

  // TODO case class Object() big syntax with define and stuff
  // TODO small syntax with various stuff
}

case class Module(declarations: Seq[Declaration])




sealed trait Declaration

object Declaration {
  case class Define(name: Name, term: Term, typ: Option[Term]) extends Declaration
  // depending on our algorithm, recursive ones might not need to declare first
  case class Declare(name: Name, typ: Term) extends Declaration
}





sealed trait Pattern

object Pattern {
  case class Atom(id: Name) extends Pattern
  case class Make(names: Seq[Pattern]) extends Pattern // TODO named patterns?
  case class Constructor(name: NameRef, pattern: Seq[Pattern]) extends Pattern
}


