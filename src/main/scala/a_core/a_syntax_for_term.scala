package a_core

abstract sealed trait Term


/**
  * we are using de Bruijn index
  */
case class LocalReference(index: Int) extends Term

case class Lambda(domain: Term, body: Term) extends Term

case class Pi(domain: Term, body: Term) extends Term

case class Application(left: Term, right: Term) extends Term



/**
  * we support global definitions by make. so a list of global definitions is just a make expression,
  * so we can support nested global definitions, definitions inside lambda etc.
  *
  * so "global reference" is a special instance of a projection, by giving Term Globally
  * you can only use it as Projection(Globally, name)
  *
  * it is trivial to support resolving  shadowed names, we don't add it now
  */
case class RecordField(name: String, body: Term) extends Term
case class Record(fields: Seq[RecordField]) extends Term

case class MakeField(name: String, body: Term) extends Term
case class Make(makes: Seq[MakeField]) extends Term

case class Projection(left: Term, right: String) extends Term

case object Globally extends Term


case class Sum(branches: Seq[(String, Term)]) extends Term

case class Construct(name: String, data: Term) extends Term

case class Split(left: Term, right: Seq[(String, Term)]) extends Term

