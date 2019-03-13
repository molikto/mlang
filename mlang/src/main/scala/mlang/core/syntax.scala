package mlang.core

import mlang.utils._


// core syntax, the goal is such that the typechecker is happy with this

enum Term {
  case Reference(depth: Int)
  case NamedReference(depth: Int, name: Unicode)
  case Pi(domain: Term, codomain: Term)
  case Lambda(domain: Term, body: Term)
  case CaseLambda(domain: Term, cases: Seq[Case])
  case Application(function: Term, argument: Term)
  case Inductive(parameters: Seq[Term], cases: Seq[Constructor])
  case Construct(name: Unicode, arguments: Seq[Term])
  case Record(fields: Seq[Field])
  case Make(definitions: Definitions)
  case Projection(make: Term, field: Unicode)
  case Universe(level: Int)

  case PathType(domain: Term, left: Term, right: Term)
  case PathAbstraction(body: Term)
  case PathApplication(abstraction: Term, argument: Dimension)
  case Transp(typ: Term, dimension: Dimension, partial: Term)
  case Hcomp(faces: Seq[Face], bottom: Term)
  // TODO univalance

  case Meta
}

sealed case class Face(dimension: Dimension, isZero: Boolean, body: Term)

enum Dimension {
  case One
  case Zero
  case Max(a: Dimension, b: Dimension)
  case Min(a: Dimension, b: Dimension)
  case Reverse(a: Dimension)
  case Reference(depth: Int)
}

type Definitions = Seq[Definition]

sealed case class Definition(name: Unicode, typ: Term)

sealed case class Field(name: Unicode, typ: Term)

sealed case class Constructor(name: Unicode, arguments: Seq[Term], typ: Term)

sealed case class Case(name: Unicode, body: Term)