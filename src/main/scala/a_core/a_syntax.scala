package a_core

import scala.collection.mutable.ArrayBuffer

sealed trait Term {
  def referencesToDefinitionsAt(i: Int): Set[String]
}


/**
  * we are using de Bruijn index
  */
case class VariableReference(index: Int) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = Set.empty
}

/**
  * record types and record values both introduce a declaration context layer
  */
case class DeclarationReference(index: Int, name: String) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = if (i == index) Set(name) else Set.empty
}

case class Lambda(domain: Term, body: Term) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = domain.referencesToDefinitionsAt(i) ++ body.referencesToDefinitionsAt(i + 1)
}

case class Pi(domain: Term, body: Term) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = domain.referencesToDefinitionsAt(i) ++ body.referencesToDefinitionsAt(i + 1)
}

case class Application(left: Term, right: Term) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = left.referencesToDefinitionsAt(i) ++ right.referencesToDefinitionsAt(i)
}
case class Cast(a: Term, b: Term) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = a.referencesToDefinitionsAt(i) ++ b.referencesToDefinitionsAt(i)
}

case class Primitive(name: String) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = Set.empty
}

sealed trait Declaration
case class TypeDeclaration(name: String, body: Term) extends Declaration
case class ValueDeclaration(name: String, body: Term) extends Declaration

case class Record(fields: Seq[TypeDeclaration]) extends Term {
  assert(fields.map(_.name).distinct.size == fields.size)

  lazy val acyclic: Seq[Seq[TypeDeclaration]] = {
    if (fields.isEmpty) {
      Seq.empty
    } else {
      val layers = new ArrayBuffer[Set[String]]()
      layers.append(Set(fields.head.name))
      var tail = fields.tail
      while (tail.nonEmpty) {
        val field = tail.head
        tail = tail.tail
        val names = field.body.referencesToDefinitionsAt(0)
        val index = layers.lastIndexWhere(_.intersect(names).nonEmpty) + 1
        if (index == layers.size) {
          layers.append(Set.empty)
        }
        layers(index) = layers(index) ++ Set(field.name)
      }
      layers.map(_.toSeq.map(n => fields.find(_.name == n).get))
    }
  }

  override def referencesToDefinitionsAt(i: Int): Set[String] = fields.map(_.body.referencesToDefinitionsAt(i + 1)).flatten.toSet
}

case class Make(declarations: Seq[Declaration]) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = declarations.map {
    case TypeDeclaration(name, body) => body.referencesToDefinitionsAt(i + 1)
    case ValueDeclaration(name, body) => body.referencesToDefinitionsAt(i + 1)
  }.flatten.toSet
}

case class Projection(left: Term, name: String) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = left.referencesToDefinitionsAt(i)
}



case class Constructor(name: String, term: Term)
case class Sum(branches: Seq[Constructor]) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = branches.map(_.term.referencesToDefinitionsAt(i)).flatten.toSet
}

case class Construct(name: String, data: Term) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = data.referencesToDefinitionsAt(i)
}

case class Branch(name: String, term: Term)
case class Split(left: Term, right: Seq[Branch]) extends Term {
  override def referencesToDefinitionsAt(i: Int): Set[String] = right.map(_.term.referencesToDefinitionsAt(i + 1)).flatten.toSet
}

//case object MetaVariable extends Term