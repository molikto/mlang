package mlang.core.checker

import mlang.core.concrete.{Name, NameRef}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer


sealed trait PatternExtractException extends CoreException

object PatternExtractException {
  class MakeWrongSize() extends PatternExtractException
  class MakeIsNotRecordType() extends PatternExtractException
  class ConstructUnknownName() extends PatternExtractException
  class ConstructWrongSize() extends PatternExtractException
  class ConstructNotSumType() extends PatternExtractException
}

sealed trait Value {
  def app(v: Value): Value = throw new IllegalArgumentException()
  def project(name: Int): Value = throw new IllegalArgumentException()
}


object Value {

  type MultiClosure = Seq[Value] => Value
  type Closure = MultiClosure

  type Stuck = Value

  sealed trait Elimination {

  }


  sealed trait AsStuck extends Value {
    override def app(v: Value): Stuck = Application(this, v)
    override def project(name: Int): Stuck = Projection(this, name)
  }

  sealed trait Spine extends AsStuck

  sealed trait ClosedReference extends Value {
    def value: Value
    override def app(v: Value): Value = value.app(v)
    override def project(name: Int): Value = value.project(name)
  }

  case class RecursiveReference(var value: Value, name: NameRef) extends ClosedReference
  case class Reference(override val value: Value, name: Name) extends ClosedReference
  case class OpenReference(id: Generic, typ: Value, name: Name) extends AsStuck

  case class Universe(level: Int) extends Value

  case class Function(domain: Value, codomain: Closure) extends Value
  /**
    * this lambda is transparent on the arguments
    */
  case class Lambda(closure: Closure) extends Value {
    override def app(v: Stuck): Stuck = closure(Seq(v))
  }
  case class Application(lambda: Stuck, argument: Value) extends Spine

  // TODO should have a field: recursive, and it must be recursive
  // TODO record should have a type

  case class RecordNode(name: Name, dependencies: Seq[NameRef], closure: MultiClosure)
  /**
    */
  case class Record(level: Int, nodes: Seq[RecordNode]) extends Value { rthis =>
    assert(nodes.isEmpty || nodes.head.dependencies.isEmpty)
    // TODO what will they became when readback??

    val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[RecordNode]): Value = {
        remaining match {
          case Seq() => Make(known)
          case _ +: tail =>
            Lambda(p => rec(known :+ p(0), tail))
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
              rec(known ++ Seq((more.name, p(0))), tail)
            })
        }
      }
      rec(Seq.empty, nodes)
    }
    def projectedType(values: Seq[Value], name: Int): Value = {
      val b = nodes(name)
      b.closure(b.dependencies.map(nodes.map(_.name).zip(values).toMap))
    }
  }

  case class Make(values: Seq[Value]) extends Value {
    override def project(name: Int): Stuck = values(name)
  }

  case class Projection(make: Stuck, field: Int) extends Spine

  case class Construct(name: NameRef, vs: Seq[Value]) extends Value
  // TODO sum should have a type, it can be indexed, so a pi type ends with type_i
  // TODO should have a field: recursive, and it must be recursive, also in case of indexed, use Constructor instead of value
  case class Constructor(name: Name, nodes: Seq[MultiClosure]) {
    val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[MultiClosure]): Value = {
        remaining match {
          case Seq() => Construct(name, known)
          case _ +: tail =>
            Lambda(p => rec(known :+ p(0), tail))
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
              rec(known :+ p(0), tail)
            })
        }
      }
      rec(Seq.empty, nodes)
    }
  }
  case class Sum(level: Int, constructors: Seq[Constructor]) extends Value {

    def constructor(name: NameRef): Option[Constructor] = constructors.find(_.name == name)

    for (c <- constructors) {
      c._makerType = c.initMakerType(this)
    }
  }

  case class Case(pattern: Pattern, closure: MultiClosure) {
    def tryApp(v: Value): Option[Value] = {
      extract(pattern, v).map(closure)
    }
  }
  
  case class PatternLambda(typ: Closure, cases: Seq[Case]) extends Value {
    // TODO overlapping patterns, we are now using first match
    override def app(v: Value): Value = {
      var res: Value = null
      var cs = cases
      while (cs.nonEmpty && res == null) {
        res = cs.head.tryApp(v).orNull
        cs = cs.tail
      }
      if (res != null) {
        res
      } else {
        PatternStuck(this, v)
      }
    }
  }

  case class PatternStuck(lambda: PatternLambda, stuck: Stuck) extends Spine



  def extractTypes(
      pattern: Pattern,
      typ: Value,
      gen: GenericGen,
      names: Int => Name = (_: Int) => ""
  ): (Seq[OpenReference], Value) = {
    val vs = mutable.ArrayBuffer[OpenReference]()
    def rec(p: Pattern, t: Value): Value = {
      p match {
        case Pattern.Atom =>
          vs.append(OpenReference(gen(), t, names(vs.size)))
          t
        case Pattern.Make(maps) =>
          typ match {
            case r@Value.Record(_, nodes) =>
              if (maps.size == nodes.size) {
                var vs =  Seq.empty[Value]
                for (m  <- maps) {
                  val it = r.projectedType(vs, vs.size)
                  val tv = rec(m, it)
                  vs = vs :+ tv
                }
                Value.Make(vs)
              } else {
                throw new PatternExtractException.MakeWrongSize()
              }
            case _ => throw new PatternExtractException.MakeIsNotRecordType()
          }
        case Pattern.Constructor(name, maps) =>
          typ match {
            case Value.Sum(_, cs) =>
              cs.find(_.name == name) match {
                case Some(c) =>
                  if (c.nodes.size == maps.size) {
                    val vs = new mutable.ArrayBuffer[Value]()
                    for ((m, n) <- maps.zip(c.nodes)) {
                      val it = n(vs)
                      val tv = rec(m, it)
                      vs.append(tv)
                    }
                    Value.Construct(name, vs)
                  } else {
                    throw new PatternExtractException.ConstructWrongSize()
                  }
                case _ =>
                  throw new PatternExtractException.ConstructUnknownName()
              }
            case _ => throw new PatternExtractException.ConstructNotSumType()
          }
      }
    }
    val t = rec(pattern, typ)
    (vs, t)
  }

  def extract(pattern: Pattern, v: Value): Option[Seq[Value]] = {
    val vs = mutable.ArrayBuffer[Value]()
    def rec(pattern: Pattern, v: Value): Boolean = {
      pattern match {
        case Pattern.Atom =>
          vs.append(v)
          true
        case Pattern.Make(names) =>
          v match {
            case Make(values) =>
              names.zip(values).forall(pair => rec(pair._1, pair._2))
            case _ =>
              false
          }
        case Pattern.Constructor(name, pattern) =>
          v match {
            case Construct(n, values) if name == n =>
              pattern.zip(values).forall(pair => rec(pair._1, pair._2))
            case _ =>
              false
          }
      }
    }
    if (rec(pattern, v)) {
      Some(vs)
    } else {
      None
    }
  }
}

