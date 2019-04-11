package mlang.core.concrete

import mlang.core.Name

sealed trait Term

case class NameType(names: Seq[Name], ty: Term)

object NameType {
  type FlatSeq = Seq[(Name.Opt, Term)]

  def flatten(names: Seq[NameType]): NameType.FlatSeq = names.flatMap(n => {
    if (n.names.isEmpty) {
      Seq((None, n.ty))
    } else {
      n.names.map(m => (Some(m), n.ty))
    }
  })
}


object Term {


  case class Universe(level: Int) extends Term

  case class Reference(name: Name.Ref) extends Term // some name is renamed

  case class Cast(term: Term, typ: Term) extends Term

  case class Function(domain: Seq[NameType], codomain: Term) extends Term
  case class Lambda(domain: Seq[Name], codomain: Term) extends Term
  case class Application(left: Term, right: Seq[Term]) extends Term

  case class Record(fields: Seq[NameType]) extends Term {
    val names = fields.flatMap(_.names)
  }
  case class Projection(left: Term, right: Name.Ref) extends Term

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
  case class Define(name: Name, typ: Option[Term], term: Term) extends Declaration
  // depending on our algorithm, recursive ones might not need to declare first
  case class Declare(name: Name, typ: Term) extends Declaration
}





sealed trait Pattern

object Pattern {
  case class Atom(id: Name) extends Pattern
  case class Make(names: Seq[Pattern]) extends Pattern // TODO named patterns?
  case class Constructor(name: Name.Ref, pattern: Seq[Pattern]) extends Pattern
}


