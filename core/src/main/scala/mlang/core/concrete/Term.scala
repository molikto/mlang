package mlang.core.concrete

sealed trait Term

object Term {
  case class Cast(term: Term, typ: Term) extends Term

  case class Reference(name: NameRef) extends Term // some name is renamed

  case class Function(domain: Term, pattern: Pattern, codomain: Term) extends Term

  case class Field(name: Name, ty: Term)
  case class Record(normalize: Boolean, fields: Seq[Field]) extends Term
  // TODO record should have a type

  case class Constructor(name: Name, term: Term) // TODO add a index term
  case class Sum(constructors: Seq[Constructor]) extends Term
  // TODO sum should have a type, it can be indexed, so a pi type ends with type_i

  case class Case(pattern: Pattern, body: Term)
  case class Lambda(domain: Option[Term], cases: Seq[Case]) extends Term

  case class Application(left: Term, right: Term) extends Term

  case class Projection(left: Term, right: NameRef) extends Term

  // TODO can you define a macro in a abstracted context?
  case class Let(declarations: Seq[Declaration], in: Term) extends Term

  // TODO case class Object() big syntax with define and stuff
  // TODO small syntax with various stuff
}

case class Module(declarations: Seq[Declaration])




sealed trait Declaration

object Declaration {
  case class Define(name: Name, term: Term, typ: Option[Term]) extends Declaration
  // TODO case class DefineFunction(name: Name, )
  // depending on our algorithm, recursive ones might not need to declare first
  case class Declare(name: Name, typ: Term) extends Declaration
}





sealed trait Pattern

object Pattern {
  case class Atom(id: Name) extends Pattern
  case class Make(maps: Seq[(NameRef, Pattern)]) extends Pattern
  case class Normalized(names: Seq[Pattern]) extends Pattern
  case class Constructor(name: NameRef, pattern: Pattern) extends Pattern
}


