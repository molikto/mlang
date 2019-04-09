package mlang.core.checker

import mlang.core.concrete.{Name, NameRef}



sealed trait Value {
  def app(v: Value): Value = throw new IllegalArgumentException()
  def project(name: NameRef): Value = throw new IllegalArgumentException()
}



object Value {

  type Closure = Value => Value
  type MultiClosure = Seq[Value] => Value

  trait Spine extends Value {
    override def app(v: Stuck): Stuck = Application(this, v)
    override def project(name: NameRef): Stuck = Projection(this, name)
  }
  type Stuck = Value

  case class Universe(level: Int) extends Value

  case class RecursiveReference(var value: Value, name: NameRef) extends Value
  case class Reference(value: Value, name: Name) extends Value
  case class OpenReference(id: Long, name: Name) extends Value

  case class Function(domain: Value, codomain: Closure) extends Value
  /**
    * this lambda is transparent on the arguments
    */
  case class Lambda(closure: Closure) extends Value {
    override def app(v: Stuck): Stuck = closure(v)
  }
  case class Application(lambda: Stuck, argument: Value) extends Spine

  // TODO should have a field: recursive, and it must be recursive
  // TODO record should have a type

  case class RecordNode(name: Name, dependencies: Seq[NameRef], closure: MultiClosure)
  /**
    */
  case class Record(nodes: Seq[RecordNode]) extends Value { rthis =>
    assert(nodes.isEmpty || nodes.head.dependencies.isEmpty)
    // TODO what will they became when readback??

    val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[RecordNode]): Value = {
        remaining match {
          case Seq() => Make(nodes.map(_.name).zip(known).toMap)
          case _ +: tail =>
            Lambda(p => rec(known :+ p, tail))
        }
      }
      rec(Seq.empty, nodes)
    }
    val makerType: Value = {
      def rec(known: Seq[(Name, Value)], remaining: Seq[RecordNode]): Value = {
        remaining match {
          case Seq() => rthis
          case Seq(head) =>
            Function(head.closure(known.filter(n => head.dependencies.contains(n._1)).map(_._2)), _ => rthis)
          case head +: more +: tail =>
            Function(head.closure(known.filter(n => head.dependencies.contains(n._1)).map(_._2)), p => {
              rec(known ++ Seq((more.name, p)), tail)
            })
        }
      }
      rec(Seq.empty, nodes)
    }
    def projectedType(values: Map[NameRef, Value], name: NameRef): Value = {
      val b = nodes.find(_.name == name).get
      b.closure(b.dependencies.map(values))
    }
  }

  case class Make(values: Map[Name, Value]) extends Value {
    override def project(name: NameRef): Stuck = values(name)
  }

  case class Projection(make: Stuck, field: Name) extends Spine

  case class Construct(name: NameRef, vs: Seq[Value]) extends Value
  // TODO sum should have a type, it can be indexed, so a pi type ends with type_i
  // TODO should have a field: recursive, and it must be recursive, also in case of indexed, use Constructor instead of value
  case class Constructor(name: Name, nodes: Seq[MultiClosure]) {
    val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[MultiClosure]): Value = {
        remaining match {
          case Seq() => Construct(name, known)
          case _ +: tail =>
            Lambda(p => rec(known :+ p, tail))
        }
      }
      rec(Seq.empty, nodes)
    }
    lazy val makerType: Value = _makerType
    private[Value] var _makerType: Value = null
    private[Value] def initMakerType(rthis: Value): Value = {
      def rec(known: Seq[Value], remaining: Seq[MultiClosure]): Value = {
        remaining match {
          case Seq() => rthis
          case Seq(head) =>
            Function(head(known), _ => rthis)
          case head +: _ +: tail =>
            Function(head(known), p => {
              rec(known :+ p, tail)
            })
        }
      }
      rec(Seq.empty, nodes)
    }
  }
  case class Sum(constructors: Seq[Constructor]) extends Value {

    for (c <- constructors) {
      c._makerType = c.initMakerType(this)
    }
  }

  sealed trait Pattern {
  }
  case class Case(pattern: Pattern, closure: MultiClosure)
  case class PatternLambda(cases: Seq[Case]) extends Value {
    override def app(v: Stuck): Stuck = ???
  }
}

