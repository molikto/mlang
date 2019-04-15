package mlang.core.checker

import mlang.core.name._
import mlang.core.utils.debug

import scala.collection.mutable


sealed trait PatternExtractException extends CoreException

object PatternExtractException {
  case class MakeWrongSize() extends PatternExtractException
  case class MakeIsNotRecordType() extends PatternExtractException
  case class ConstructUnknownName() extends PatternExtractException
  case class ConstructWrongSize() extends PatternExtractException
  case class ConstructNotSumType() extends PatternExtractException
}

sealed trait Value {
  // also used to decide how
  def app(v: Value, env: Reduction = Reduction.Default): Value = env.app.map(r => {
    this match {
      case Value.Lambda(closure) => closure(v, r)
      case p@Value.PatternLambda(_, _, cases) =>
        // TODO overlapping patterns, we are now using first match
        var res: Value = null
        var cs = cases
        while (cs.nonEmpty && res == null) {
          res = cs.head.tryApp(v, r).orNull
          cs = cs.tail
        }
        if (res != null) {
          res
        } else {
          Value.PatternStuck(p, v)
        }
      case _ =>
        Value.Application(this, v)
    }
  }).getOrElse(Value.Application(this, v))

  def project(name: Int, env: Reduction = Reduction.Default): Value = if (env.project) {
    this match {
      case Value.Make(vs) => vs(name)
      case _ => Value.Projection(this, name)
    }
  } else {
    Value.Projection(this, name)
  }

  def delet(env: Reduction = Reduction.Default): Value =
    if (env.delet) {
      this match {
        case v: Value.Let => v.body.delet(env)
        case _ => this
      }
    } else {
      this
    }

  def deref(env: Reduction = Reduction.Default): Value =
    if (env.deref == Reduction.Deref.All) {
      this match {
        case v: Value.ClosedReference => v.value.deref(env)
        case _ => this
      }
    } else if (env.deref == Reduction.Deref.NonRecursive) {
      this match {
        case v: Value.Reference => v.value.deref(env)
        case _ => this
      }
    } else {
      this
    }
}


object Value {

  implicit class MultiClosure(private val func: (Seq[Value], Reduction) => Value) extends AnyVal {
    def apply(seq: Seq[Value], reduction: Reduction = Reduction.Default): Value = func(seq, reduction)
  }

  implicit class Closure(private val func: (Seq[Value], Reduction) => Value) extends AnyVal {
    def apply(seq: Value, reduction: Reduction = Reduction.Default): Value = func(Seq(seq), reduction)
  }

  type Stuck = Value

  sealed trait Elimination {

  }


  sealed trait AsStuck extends Value

  sealed trait Spine extends AsStuck

  sealed trait ClosedReference extends Value {
    def value: Value
  }

  // the var is a total hack!! but it is very beautiful!!!
  case class RecursiveReference(value: Value, typ: Value) extends ClosedReference {
    debug("recursive reference created")
  }
  case class Reference(value: Value) extends ClosedReference
  case class OpenReference(id: Generic, typ: Value) extends AsStuck

  case class Universe(level: Int) extends Value

  case class Function(domain: Value, codomain: Closure) extends Value
  case class Application(lambda: Stuck, argument: Value) extends Spine

  // TODO should have a field: recursive, and it must be recursive
  // TODO record should have a type

  case class RecordNode(name: Name, dependencies: Seq[Ref], closure: MultiClosure)

  case class Record(level: Int, nodes: Seq[RecordNode]) extends Value { rthis =>
    assert(nodes.isEmpty || nodes.head.dependencies.isEmpty)
    // TODO what will they became when readback??

    lazy val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[RecordNode], r: Reduction): Value = {
        remaining match {
          case Seq() => Make(known)
          case _ +: tail =>
            Lambda(Closure((p, r) => rec(known :+ p.head, tail, r)))
        }
      }
      rec(Seq.empty, nodes, Reduction.Default)
    }

    lazy val makerType: Value = {
      def rec(known: Seq[(Ref, Value)], remaining: Seq[RecordNode], r: Reduction): Value = {
        remaining match {
          case Seq() => rthis
          case Seq(head) =>
            Function(head.closure(known.filter(n => head.dependencies.contains(n._1)).map(_._2)), Closure((_, _) => rthis))
          case head +: more +: tail =>
            Function(head.closure(known.filter(n => head.dependencies.contains(n._1)).map(_._2)), Closure((p, r) => {
              rec(known ++ Seq((more.name.refSelf, p.head)), tail, r)
            }))
        }
      }
      rec(Seq.empty, nodes, Reduction.Default)
    }
    def projectedType(values: Seq[Value], name: Int): Value = {
      val b = nodes(name)
      b.closure(b.dependencies.map(nodes.map(_.name.refSelf).zip(values).toMap))
    }
  }

  case class Make(values: Seq[Value]) extends Value

  case class Projection(make: Stuck, field: Int) extends Spine

  case class Construct(name: Tag, vs: Seq[Value]) extends Value
  // TODO sum should have a type, it can be indexed, so a pi type ends with type_i
  // TODO should have a field: recursive, and it must be recursive, also in case of indexed, use Constructor instead of value
  case class Constructor(name: Tag, parameters: Int, nodes: Seq[MultiClosure]) {
    lazy val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[MultiClosure], r: Reduction): Value = {
        remaining match {
          case Seq() => Construct(name, known)
          case _ +: tail =>
            Lambda(Closure((p, r) => rec(known :+ p.head, tail, r)))
        }
      }
      rec(Seq.empty, nodes, Reduction.Default)
    }
    private[Value] var _sum: Sum = _
    lazy val makerType: Value = {
      def rec(known: Seq[Value], remaining: Seq[MultiClosure], r: Reduction): Value = {
        remaining match {
          case Seq() => _sum
          case Seq(head) =>
            Function(head(known), Closure((_, _) => _sum))
          case head +: _ +: tail =>
            Function(head(known), Closure((p, r) => {
              rec(known :+ p.head, tail, r)
            }))
        }
      }
      rec(Seq.empty, nodes, Reduction.Default)
    }
  }
  case class Sum(level: Int, constructors: Seq[Constructor]) extends Value {
    for (c <- constructors) {
      c._sum = this
    }
  }

  case class Case(pattern: Pattern, closure: MultiClosure) {
    def tryApp(v: Value, r: Reduction): Option[Value] = {
      extract(pattern, v).map(a => closure(a, r))
    }
  }

  /**
    * this lambda is transparent on the arguments
    */
  case class Lambda(closure: Closure) extends Value

  case class PatternLambda(id: Generic, typ: Closure, cases: Seq[Case]) extends Value

  case class PatternStuck(lambda: PatternLambda, stuck: Stuck) extends Spine

  object Let {
    case class Item(value: Value, typ: Option[Value])
  }
  case class Let(var items: Seq[Let.Item], body: Value) extends Value



  def extractTypes(
      pattern: Pattern,
      @canrecur typ: Value,
      gen: GenericGen
  ): (Seq[OpenReference], Value) = {
    val vs = mutable.ArrayBuffer[OpenReference]()
    def rec(p: Pattern, @canrecur t: Value): Value = {
      p match {
        case Pattern.Atom =>
          val ret = OpenReference(gen(), t)
          vs.append(ret)
          ret
        case Pattern.Make(maps) =>
          t match {
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
                throw PatternExtractException.MakeWrongSize()
              }
            case _ => throw PatternExtractException.MakeIsNotRecordType()
          }
        case Pattern.Construct(name, maps) =>
          t match {
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
                    throw PatternExtractException.ConstructWrongSize()
                  }
                case _ =>
                  throw PatternExtractException.ConstructUnknownName()
              }
            case _ => throw PatternExtractException.ConstructNotSumType()
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
        case Pattern.Construct(name, pt) =>
          v match {
            case Construct(n, values) if name == n =>
              pt.zip(values).forall(pair => rec(pair._1, pair._2))
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

