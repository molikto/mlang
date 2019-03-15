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

  enum Dependency {
    case CanMutual, CannotMutual
  }

  sealed case class Parameter(name: Unicode, term: Term)

  sealed case class Case(name: Unicode, fields: Seq[Unicode], body: Term)

  sealed case class Constructor(name: Unicode, arguments: Seq[Parameter], typ: Term)

  // sealed case class Face(dimension: Dimension, isZero: Boolean, body: Term)


  type Dependencies = Map[Unicode, Dependency]

  sealed case class Definition(name: Unicode, term: Term) {

    def dependencies(names: Set[Unicode]): Dependencies = {
      def join(a: Dependencies, b: Dependencies): Dependencies = {
        a.mergeWith(b, { (v, v2) =>
          v match {
            case Dependency.CanMutual => v
            case _ => v2
          }
        })
      }

      def flatten(a: Seq[Dependencies]): Dependencies = {
        a match {
          case (h +: t) => join(h, flatten(t))
          case Nil => Map.empty
        }
      }
      def recDefs(fs: Seq[Definition], alive: Set[Unicode], dependency: Dependency) = {
        val av = alive -- fs.map(_.name)
        flatten(fs.map(f => rec(f.term, av, dependency)))
      }
      def recParams(fs: Seq[Parameter], alive: Set[Unicode], dependency: Dependency): Dependencies = {
        fs match {
          case (h +: t) => join(rec(h.term, alive, dependency), recParams(t, alive - h.name, dependency))
          case Nil => Map.empty
        }
      }
      def recCt(c: Constructor, alive: Set[Unicode], dependency: Dependency): Dependencies = {
        join(recParams(c.arguments, alive, dependency), rec(c.typ, alive -- c.arguments.map(_.name), dependency))
      }
      def rec(tm: Term, alive: Set[Unicode], dependency: Dependency): Dependencies = {
        tm match {
          case Reference(name) =>
            if (alive.contains(name)) Map(name -> dependency) else Map.empty
          case Ascription(body, typ) =>
            join(rec(body, alive, dependency), rec(typ, alive, dependency))
          case Application(lambda, argument) =>
            join(rec(lambda, alive, dependency), rec(argument, alive, dependency))
          case Projection(term, field) =>
            rec(term, alive, dependency)
          case Inductive(parameters, constructors) =>
            val dp = Dependency.CannotMutual
            val av = alive -- parameters.map(_.name)
            join(recParams(parameters, alive, dp), flatten(constructors.map(c => recCt(c, av, dp))))
          case Pi(name: Unicode, domain: Term, codomain: Term) =>
            join(rec(domain, alive, dependency), rec(codomain, alive - name, dependency))
          case Record(fields) =>
            recDefs(fields, alive, dependency)
          case Lambda(name, body) =>
            rec(body, alive - name, dependency)
          case CaseLambda(cases) =>
            flatten(cases.map(c => rec(c.body, alive -- c.fields, dependency)))
          case Construct(name, arguments) =>
            flatten(arguments.map(a => rec(a, alive, dependency)))
          case Make(fields, dependent) =>
            recDefs(fields, alive, dependency)
          case Universe(level) =>
            Map.empty
        }
      }
      rec(term, names, Dependency.CanMutual)
    }
  }
}

import Term._

enum Term {
  case Reference(name: Unicode) // recursive or not??

  case Ascription(body: Term, typ: Term)
  
  case Application(lambda: Term, argument: Term)
  case Projection(term: Term, field: Unicode)

  case Inductive(parameters: Seq[Parameter], constructors: Seq[Constructor])
  case Pi(name: Unicode, domain: Term, codomain: Term)
  case Record(fields: Seq[Definition])

  case Lambda(name: Unicode, body: Term)
  case CaseLambda(cases: Seq[Case])
  case Construct(name: Unicode, arguments: Seq[Term])
  case Make(fields: Seq[Definition], dependent: Boolean)

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

