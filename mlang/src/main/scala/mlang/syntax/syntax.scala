package mlang.syntax

import mlang.utils._

// surface syntax is a **equivalence** of what user write, now is not complicated, wait for the editor


// enum Dimension {
//   case One
//   case Zero
//   case Max(a: Dimension, b: Dimension)
//   case Min(a: Dimension, b: Dimension)
//   case Reverse(a: Dimension)
//   case Reference(name: Unicode)
// }

object Term {
  sealed case class Case(name: Unicode, fields: Seq[Unicode], body: Term)

  sealed case class Constructor(name: Unicode, arguments: Seq[Term], typ: Term)

  // sealed case class Face(dimension: Dimension, isZero: Boolean, body: Term)

  sealed case class Field(name: Unicode, typ: Term)

  sealed case class Definition(name: Unicode, term: Term)
}

import Term._

enum Term {
  case Reference(name: Unicode) // recursive or not??

  case Ascription(body: Term, typ: Term)
  
  case Application(lambda: Term, argument: Term)
  case Projection(term: Term, field: Unicode)

  case Inductive(parameters: Seq[Term], typ: Term, constructors: Seq[Constructor])
  case Pi(name: Unicode, domain: Term, codomain: Term)
  case Record(fields: Seq[Field])

  case Lambda(name: Unicode, body: Term)
  case CaseLambda(cases: Seq[Case])
  case Construct(name: Unicode, arguments: Seq[Term])
  case Make(fields: Seq[Definition])

  case Universe(level: Int)
  /*
  case PathType(name: Unicode, domain: Term, left: Term, right: Term)
  case PathAbstraction(name: Unicode, body: Term)
  case PathApplication(abstraction: Term, argument: Dimension)
  case Transp(name: Unicode, typ: Term, dimension: Dimension, partial: Term)
  case Hcomp(faces: Seq[Face], bottom: Term)
  */
  // TODO univalance terms
  //case Omitted
}

