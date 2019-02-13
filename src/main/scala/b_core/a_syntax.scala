package b_core

import scala.collection.mutable.ArrayBuffer

sealed trait Term {
  def collectReferences(i: Int): Set[String]
}


/**
  * currently some term is "core" as they can be readback as. some is not, as "cast" we discard them in value world
  */
case class VariableReference(index: Int) extends Term {
  override def collectReferences(i: Int): Set[String] = Set.empty
}

/**
  * record types and record values both introduce a declaration context layer
  */
case class DeclarationReference(index: Int, name: String) extends Term {
  override def collectReferences(i: Int): Set[String] = if (i == index) Set(name) else Set.empty
}

case class Lambda(domain: Term, body: Term) extends Term {
  override def collectReferences(i: Int): Set[String] = domain.collectReferences(i) ++ body.collectReferences(i + 1)
}

case class Pi(domain: Term, body: Term) extends Term {
  override def collectReferences(i: Int): Set[String] = domain.collectReferences(i) ++ body.collectReferences(i + 1)
}

case class Application(left: Term, right: Term) extends Term {
  override def collectReferences(i: Int): Set[String] = left.collectReferences(i) ++ right.collectReferences(i)
}

case class Primitive(name: String) extends Term {
  override def collectReferences(i: Int): Set[String] = Set.empty
}

object Primitive {
  val names = PrimitiveValues.keys
}

sealed trait Declaration
case class TypeDeclaration(name: String, body: Term) extends Declaration
case class ValueDeclaration(name: String, body: Term) extends Declaration

case class Record(fields: Seq[TypeDeclaration]) extends Term {
  assert(fields.map(_.name).distinct.size == fields.size)

  val nonDependentLayers: Seq[Seq[String]] = {
    if (fields.isEmpty) {
      Seq.empty
    } else {
      val layers = new ArrayBuffer[Set[String]]()
      layers.append(Set(fields.head.name))
      var tail = fields.tail
      while (tail.nonEmpty) {
        val field = tail.head
        tail = tail.tail
        val names = field.body.collectReferences(0)
        val index = layers.lastIndexWhere(_.intersect(names).nonEmpty) + 1
        if (index == layers.size) {
          layers.append(Set.empty)
        }
        layers(index) = layers(index) ++ Set(field.name)
      }
      layers.map(_.toSeq)
    }
  }

  override def collectReferences(i: Int): Set[String] = fields.map(_.body.collectReferences(i + 1)).flatten.toSet
}

case class Make(declarations: Seq[Declaration]) extends Term {
  override def collectReferences(i: Int): Set[String] = declarations.map {
    case TypeDeclaration(name, body) => body.collectReferences(i + 1)
    case ValueDeclaration(name, body) => body.collectReferences(i + 1)
  }.flatten.toSet

  val valueDeclarations = declarations.flatMap {
    case v: ValueDeclaration => Some(v)
    case _ => None
  }

  val directValueDependencies: Map[String, Set[String]] = {
    valueDeclarations.map(a => a.name -> a.body).toMap.mapValues(_.collectReferences(0))
  }

  val mutualDependencies: Set[Set[String]] =
    a_utils.GraphAlgorithms.tarjanCcc(directValueDependencies).filter(a => a.size > 1 || directValueDependencies(a.head).contains(a.head))
}

case class Projection(left: Term, name: String) extends Term {
  override def collectReferences(i: Int): Set[String] = left.collectReferences(i)
}



case class Constructor(name: String, term: Term)
case class Sum(branches: Seq[Constructor]) extends Term {
  override def collectReferences(i: Int): Set[String] = branches.map(_.term.collectReferences(i)).flatten.toSet
}

case class Construct(name: String, data: Term) extends Term {
  override def collectReferences(i: Int): Set[String] = data.collectReferences(i)
}

case class Branch(name: String, term: Term)
case class Split(left: Term, right: Seq[Branch]) extends Term {
  override def collectReferences(i: Int): Set[String] = right.map(_.term.collectReferences(i + 1)).flatten.toSet
}

/**
  *
  *
  *
  * non-essential ones
  *
  *
  *
  */

//case object MetaVariable extends Term

case class Cast(a: Term, b: Term) extends Term {
  override def collectReferences(i: Int): Set[String] = a.collectReferences(i) ++ b.collectReferences(i)
}
