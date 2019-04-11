package mlang.core.concrete

sealed trait Term

sealed trait Block

case class NamesType(name: Seq[Name], ty: Term)

object Term {
  case class Universe(level: Int) extends Term

  case class Reference(name: NameRef) extends Term // some name is renamed

  case class Cast(term: Term, typ: Term) extends Term

  case class Function(domain: Seq[NamesType], codomain: Term) extends Term
  case class Lambda(name: Seq[Name], codomain: Term) extends Term
  case class Application(left: Term, right: Term) extends Term

  case class Record(fields: Seq[NamesType]) extends Term with Block
  case class Projection(left: Term, right: NameRef) extends Term

  case class Constructor(name: Name, term: Seq[NamesType])
  case class Sum(constructors: Seq[Constructor]) extends Term with Block

  case class Case(pattern: Pattern, body: Term)
  case class PatternLambda(branches: Seq[Case]) extends Term with Block

  // TODO can you define a macro in a abstracted context?
  case class Let(declarations: Seq[Declaration], in: Term) extends Term with Block

  // TODO case class Object() big syntax with define and stuff
  // TODO make small syntax with various stuff, type is inferred as non-dependent
  // TODO local match and local tree split
}

case class Module(declarations: Seq[Declaration])




sealed trait Declaration

object PatternTree {
  type Body = Either[Term, Seq[PatternTree]]
}

case class PatternTree(skip: Seq[OptName], branches: Seq[(Pattern, PatternTree.Body)])

object Declaration {
  case class Define(name: Name, tele: Seq[NamesType], typ: Option[Term], term: PatternTree.Body) extends Declaration
  // depending on our algorithm, recursive ones might not need to declare first
  case class Declare(name: Name, tele: Seq[NamesType], typ: Term) extends Declaration
}





sealed trait Pattern

object Pattern {
  case class Atom(id: Name) extends Pattern
  case class Make(names: Seq[Pattern]) extends Pattern // TODO named patterns?
  case class Constructor(name: NameRef, pattern: Seq[Pattern]) extends Pattern
}


