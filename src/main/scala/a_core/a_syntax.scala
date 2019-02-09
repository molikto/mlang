package a_core

sealed trait Term


/**
  * we are using de Bruijn index
  */
case class VariableReference(index: Int) extends Term

/**
  * record types and record values both introduce a declaration context layer
  */
case class DeclarationReference(index: Int, name: String) extends Term

case class Lambda(domain: Term, body: Term) extends Term

case class Pi(domain: Term, body: Term) extends Term

case class Application(left: Term, right: Term) extends Term

sealed trait Declaration
case class TypeDeclaration(name: String, body: Term) extends Declaration
case class ValueDeclaration(name: String, body: Term) extends Declaration

case class Record(acyclic: Seq[Seq[TypeDeclaration]]) extends Term {
  assert(acyclic.flatten.map(_.name).distinct.size == acyclic.flatten.size)
}

case class Make(declarations: Seq[Declaration]) extends Term {
}

case class Projection(left: Term, name: String) extends Term



case class Constructor(name: String, term: Term)
case class Sum(branches: Seq[Constructor]) extends Term

case class Construct(name: String, data: Term) extends Term

case class Branch(name: String, term: Term)
case class Split(left: Term, right: Seq[Branch]) extends Term

//case object MetaVariable extends Term