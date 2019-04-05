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

  sealed case class Case(name: Unicode, fields: Seq[Unicode], body: Term)

  sealed case class Constructor(name: Unicode, arguments: Seq[Parameter], typ: Term)

  // sealed case class Face(dimension: Dimension, isZero: Boolean, body: Term)

  type Dependencies = Map[Unicode, Dependency]

  trait Parameters {
    def terms: Seq[Parameter]

    lazy val directDependencies: Map[Unicode, Dependencies] = {
      val names = terms.map(_.name).toSet
      terms.map(a => a.name -> a.directDependencies(names)).toMap
    }

    def avg: Option[Seq[Set[Unicode]]] = {
      var remaining = directDependencies.mapValues(a => a.keySet)
      var collect = Seq.empty[Set[Unicode]]
      var cont = true
      while (remaining.nonEmpty && cont) {
        val newOnes = remaining.filter(_._2.isEmpty).keySet
        if (newOnes.isEmpty) {
          cont = false
        } else {
          collect = collect :+ newOnes
          remaining = (remaining -- newOnes).mapValues(_ -- newOnes)
        }
      }
      if (cont) {
        Some(collect)
      } else {
        None
      }
    }

    // val recursiveDependencies: Set[Set[String]] = 
    //   tarjanCcc(directDependencies.mapValues(_.keySet)).filter(a => a.size > 1 || directDependencies(a.head).contains(a.head))
  }


  sealed case class Parameter(name: Unicode, term: Term) {

    def directDependencies(names: Set[Unicode]): Dependencies = {
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
      def recSeq(fs: Seq[Term], alive: Set[Unicode], dependency: Dependency): Dependencies = {
        flatten(fs.map(f => rec(f, alive, dependency)))
      }
      def recCt(c: Constructor, alive: Set[Unicode], dependency: Dependency): Dependencies = {
        val av = alive -- c.arguments.map(_.name)
        join(recSeq(c.arguments.map(_.term), av, dependency), rec(c.typ, av, dependency))
      }

      def rec(tm: Term, alive: Set[Unicode], dependency: Dependency): Dependencies = {
        tm match {
          case Reference(name) =>
            if (alive.contains(name)) Map(name -> dependency) else Map.empty
          case Ascription(body, typ) =>
            join(rec(body, alive, dependency), rec(typ, alive, dependency))
          case Pi(parameters, codomain) =>
            val av = alive -- parameters.map(_.name)
            join(recSeq(parameters.map(_.term), av, dependency), rec(codomain, av, dependency))
          case Lambda(names, body) =>
            rec(body, alive -- names, dependency)
          case Application(lambda, arguments) =>
            join(rec(lambda, alive, dependency), recSeq(arguments, alive, dependency))
          case Inductive(parameters, constructors) =>
            val dp = Dependency.CannotMutual
            val av = alive -- parameters.map(_.name)
            join(recSeq(parameters.map(_.term), alive, dp), flatten(constructors.map(c => recCt(c, av, dp))))
          case Record(parameters) =>
            val av = alive -- parameters.map(_.name)
            recSeq(parameters.map(_.term), alive, dependency)
          case Construct(name, arguments) =>
            recSeq(arguments, alive, dependency)
          case Make(parameters, dependent) =>
            val av = alive -- parameters.map(_.name)
            recSeq(parameters.map(_.term), alive, dependency)
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

  case Ascription(term: Term, typ: Term)

  // pi type consists a domain, and a function term => term
  case Pi(domain: Term, codomain: Term)
  // 
  case Application(left: Term, argument: Term)

  case Inductive(parameters: Seq[Parameter], constructors: Seq[Constructor])
  case Construct(name: Unicode, arguments: Seq[Term])

  case Record(override val terms: Seq[Parameter]) extends Term with Parameters
  case Make(override val terms: Seq[Parameter], dependent: Boolean) extends Term with Parameters

  case PatternMatching(patterns: ) // TODO pattern matching
  case CopatternMatching()

  case Universe(level: Int)
  /*

  ones = { head: 1, tail: ones }

  id: N => N = app(n, )


  case PathType(name: Unicode, domain: Term, left: Term, right: Term)
  case PathAbstraction(name: Unicode, body: Term)
  case PathApplication(abstraction: Term, argument: Dimension)
  case Transp(name: Unicode, typ: Term, dimension: Dimension, partial: Term)
  case Hcomp(faces: Seq[Face], bottom: Term)
  */
  // TODO univalance terms
  //case Omitted
}
