package mlang.core

import mlang.name._

import scala.collection.mutable


sealed trait PatternExtractException extends CoreException


object PatternExtractException {
  case class MakeWrongSize() extends PatternExtractException
  case class MakeIsNotRecordType() extends PatternExtractException
  case class ConstructUnknownName() extends PatternExtractException
  case class ConstructWrongSize() extends PatternExtractException
  case class ConstructNotSumType() extends PatternExtractException
}

import Value._



sealed trait Value {


  def restrict(lv: DimensionPair): Value = this match {
    case u: Universe => u
    case Function(domain, codomain) =>
      Function(domain.restrict(lv), codomain.restrict(lv))
    case Record(level, nodes) =>
      Record(level, nodes.map(n => RecordNode(n.name, n.dependencies, n.closure.restrict(lv))))
    case Make(values) =>
      Make(values.map(_.restrict(lv)))
    case Construct(name, vs) =>
      Construct(name, vs.map(_.restrict(lv)))
    case Sum(level, constructors) =>
      Sum(level, constructors.map(n => Constructor(n.name, n.parameters, n.nodes.map(_.restrict(lv)))))
    case Lambda(closure) =>
      Lambda(closure.restrict(lv))
    case PatternLambda(id, typ, cases) =>
      PatternLambda(id, typ.restrict(lv), cases.map(a => Case(a.pattern, a.closure.restrict(lv))))
    case PathType(typ, left, right) =>
      PathType(typ.restrict(lv), left.restrict(lv), right.restrict(lv))
    case PathLambda(body) =>
      PathLambda(body.restrict(lv))
    case Application(lambda, argument) =>
      Application(lambda.restrict(lv), argument.restrict(lv))
    case Restricted(a, restriction) =>
      Restricted(a.restrict(lv), restriction)
    case Coe(direction, tp, base) =>
      Coe(direction, tp.restrict(lv), base.restrict(lv))
    case Hcom(direction, tp, base, restrictions) =>
      Hcom(direction, tp.restrict(lv), base.restrict(lv), restrictions.map(n => Restriction(n.pair, n.body.restrict(lv))))
    case Maker(value, field) =>
      Maker(value.restrict(lv), field)
    case Projection(make, field) =>
      Projection(make.restrict(lv), field)
    case PatternStuck(lambda, stuck) =>
      PatternStuck(lambda.restrict(lv).asInstanceOf[PatternLambda], stuck.restrict(lv))
    case Let(items, order, body) =>
      Let(items.map(_.restrict(lv)), order, body.restrict(lv))
    case PathApplication(left, stuck) =>
      PathApplication(left.restrict(lv), stuck.restrict(lv))
    case o: Reference =>
      Restricted(o, lv)
    case o: OpenReference =>
      Restricted(o, lv)
  }


  final override def equals(obj: Any): Boolean = {
    throw new IllegalArgumentException("Values don't have equal. Either call eq or do conversion checking")
  }

  private var _whnf: Value = _
  private var _nf: Value = _

  // LATER what's the relationship between whnf and reduction class?
  // reduction mainly used to determine the way a closure is evaluated
  // a value itself that contains redux can be evaluated by whnf and normalize two method
  def whnf: Value = {
    if (_whnf == null) {
      _whnf = this match {
        case a: HeadCanonical =>
          a
        case r: Reference =>
          r.deref(Reduction.Deref.All).whnf
        case o: OpenReference =>
          o
        case Application(lambda, argument) =>
          lambda.whnf.app(argument, Reduction.App.Once, true)
        case Projection(make, field) =>
          make.whnf.project(field, Reduction.Project, true)
        case PatternStuck(lambda, stuck) =>
          lambda.app(stuck.whnf, Reduction.App.Once, true)
        case Coe(direction, tp, stuck) =>
          stuck.whnf.coe(direction, tp, Reduction.Kan.Once, true)
        case Hcom(direction, tp, stuck, restrictions) =>
          stuck.whnf.hcom(direction, tp, restrictions, Reduction.Kan.Once, true)
        case Restricted(a, restriction) =>
          a.whnf.restrict(restriction)
        case Maker(r, i) =>
          // this is a lambda or make expression so in whnf
          r.whnf.demaker(i, Reduction.Normalize)
        case Let(_, _, body) =>
          body.whnf
        case PathApplication(left, stuck) =>
          left.whnf.papp(stuck, Reduction.Papp.Once, true)
      }
      _whnf._whnf = _whnf
    }
    _whnf
  }

  // renormalize. save some evaluator string
  def renor(r: Reduction): Value = {
    if (r.renor) {
      this.normalize
    } else {
      this
    }
  }


  private def normalizeWhnfStuck(a: Value): Value = {
    a match {
      case OpenReference(id, typ) =>
        OpenReference(id, typ.normalize)
      case Application(lambda, argument) =>
        Application(normalizeWhnfStuck(lambda), argument.normalize)
      case Projection(make, field) =>
        Projection(normalizeWhnfStuck(make), field)
      case PatternStuck(lambda, stuck) =>
        PatternStuck(lambda, normalizeWhnfStuck(stuck))
      case PathApplication(left, stuck) =>
        PathApplication(left.normalize, stuck)
      case _ => logicError()
    }
  }

  def normalize: Value = {
    if (_nf == null) {
      _nf = this.whnf match {
        case a: Universe =>
          a
        case Function(domain, codomain) =>
          Function(domain.normalize, codomain)
        case r:Record =>
          r
        case s: Sum =>
          s
        case p: PatternLambda =>
          p
        case l: Lambda =>
          l
        case p: PathLambda =>
          p
        case Make(values) =>
          Make(values.map(_.normalize))
        case Construct(name, vs) =>
          Construct(name, vs.map(_.normalize))
        case PathType(typ, left, right) =>
          PathType(typ, left.normalize, right.normalize)
        case _: Reference => logicError()
        case _: Maker => logicError()
        case _: Let => logicError()
        case a =>
          normalizeWhnfStuck(a)
      }
      _nf._nf = _nf
    }
    _nf
  }

  private def wh(a: Value, b: Boolean): Value = if (b) a.whnf else a

  // also used to decide how
  def app(v: Value, env: Reduction /* REDUCTION */, whnf: Boolean = false): Value = env.app.map(r => {
    this match {
      case Lambda(closure) =>
        wh(closure(v, r), whnf)
      case p@PatternLambda(_, _, cases) =>
        // TODO overlapping patterns, we are now using first match
        var res: Value = null
        var cs = cases
        while (cs.nonEmpty && res == null) {
          res = cs.head.tryApp(v, r).orNull
          cs = cs.tail
        }
        if (res != null) {
          wh(res, whnf)
        } else {
          PatternStuck(p, v)
        }
      case _ =>
        Application(this, v)
    }
  }).getOrElse(Application(this, v))


  def coe(pair: DimensionPair, typ: PathClosure, env: Reduction, whnf: Boolean = false): Value =  env.kan.map({ r =>
    if (pair.from == pair.to) { // just to base
      wh(this, whnf)
    } else {
      // this is ok?
      typ(Dimension.True, env).whnf match {
        case Function(_, _) =>
          def func(a: Value): Function = a.whnf match {
            case f@Function(_, _) => f
            case _ => logicError()
          }
          Lambda(Value.Closure((a, r) => {
            val a_ = a.head.coe(pair.reverse, typ.map(a => func(a).domain), r)
            val app_ = this.app(a_, r)
            app_.coe(pair, typ.mapd((f, d) => func(f).codomain(a.head.coe(DimensionPair(pair.to, d), typ.map(a => func(a).domain), r), r)), r)
          }))
        case _ =>
          ???
      }
    }
  }).getOrElse(Coe(pair, typ, this))

  def hcom(pair: DimensionPair, typ: Value, restriction0: Seq[Restriction], env: Reduction, whnf: Boolean = false): Value = {
    val restriction = restriction0.filter(_.pair.isFalse)
    env.kan.map({ r =>
      if (pair.from == pair.to) {
        wh(this, whnf)
      } else {
        restriction.find(a => a.pair.from == a.pair.to) match { // always true face
          case Some(n) =>
            wh(n.body(pair.to, r), whnf)
          case None =>
            typ.whnf match {
              case Function(_, codomain) =>
                Lambda(Value.Closure((a, r) => this.app(a.head, r).hcom(
                  pair,
                  codomain(a.head, r),
                  restriction.map(n => Restriction(n.pair, n.body.map(_.app(a.head, r)))), r)))
              case _ =>
                ???
            }
        }
      }
    }).getOrElse(Hcom(pair, typ, this, restriction))
  }

  def papp(d: Dimension, env: Reduction /* REDUCTION */, whnf: Boolean = false): Value = env.papp.map(r => {
    this match {
      case PathLambda(c) =>
        wh(c(d, r), whnf)
      case a =>
        d match {
          case Dimension.Constant(i) =>
            infer(a, env).whnf match {
              case PathType(_, left, right) =>
                wh(if (i) right else left, whnf)
              case _ => logicError()
            }
          case _: Dimension.OpenReference =>
            PathApplication(this, d)
        }
    }
  }).getOrElse(PathApplication(this, d))


  def makerType(i: Int): Value = this.whnf match {
    case s: Sum => s.constructors(i).makerType
    case v: Record => v.makerType
    case _ => logicError()
  }

  def demaker(i: Int, env: Reduction /* REDUCTION */): Value = if (env.demaker) {
    this match {
      case s: Sum => s.constructors(i).maker
      case r: Record =>
        assert(i == -1)
        r.maker
      case _ => Maker(this, i)
    }
  } else {
    Maker(this, i)
  }

  def project(name: Int, env: Reduction /* REDUCTION */, whnf: Boolean = false): Value = if (env.project) {
    this match {
      case Make(vs) => wh(vs(name), whnf)
      case _ => Projection(this, name)
    }
  } else {
    Projection(this, name)
  }

  def delet(env: Reduction /* REDUCTION */): Value =
    if (env.delet) {
      this match {
        case v: Let => v.body.delet(env)
        case _ => this
      }
    } else {
      this
    }

  def deref(env: Reduction /* REDUCTION */): Value =
    if (env.deref == Deref.Normalize) {
      this match {
        case v: Reference => v.value.deref(env).normalize
        case o: OpenReference => o.copy(typ = o.typ.normalize)
        case _ => this
      }
    } else if (env.deref == Deref.All) {
      this match {
        case v: Reference => v.value.deref(env)
        case _ => this
      }
    } else if (env.deref == Deref.NonRecursive) {
      this match {
        case v: Reference if v.closed == 0 => v.value.deref(env)
        case _ => this
      }
    } else {
      this
    }
}


object Value {

  implicit class MultiClosure(private val func: (Seq[Value], Reduction) => Value) extends AnyVal {
    def apply(seq: Seq[Value], reduction: Reduction /* REDUCTION */): Value = func(seq, reduction)
    def restrict(lv: DimensionPair) = Value.MultiClosure((v, r) => this(v, r).restrict(lv))
  }

  implicit class Closure(private val func: (Seq[Value], Reduction) => Value) extends AnyVal {
    def apply(seq: Value, reduction: Reduction /* REDUCTION */): Value = func(Seq(seq), reduction)
    def restrict(lv: DimensionPair) = Value.Closure((v, r) => this(v.head, r).restrict(lv))
  }

  object Closure {
    def apply(a: Value): Closure = Closure((_, r) => a.renor(r))
  }

  object PathClosure {
    def apply(a: Value): PathClosure = PathClosure((_, r) => a.renor(r))
  }

  implicit class PathClosure(private val func: (Dimension, Reduction) => Value) extends AnyVal {
    def apply(seq: Dimension, reduction: Reduction /* REDUCTION */): Value = func(seq, reduction)
    def restrict(lv: DimensionPair): PathClosure = Value.PathClosure((v, r) => this(v, r).restrict(lv))
    def mapd(a: (Value, Dimension) => Value): PathClosure = PathClosure((d, r) => a(this(d, r), d))
    def map(a: Value => Value): PathClosure = PathClosure((d, r) => a(this(d, r)))
  }


  case class DimensionPair(from: Dimension, to: Dimension) {
    def reverse: DimensionPair = DimensionPair(to, from)

    def isFalse: Boolean = (from == Dimension.False && to == Dimension.True) || (from == Dimension.True && to == Dimension.False)

  }

  sealed trait Dimension extends {
    def matches(id: Generic): Boolean = this match {
      case Dimension.OpenReference(iid) => iid == id
      case Dimension.Constant(_) => false
    }

    def max(t: Dimension): Dimension = (this, t) match {
      case (Dimension.OpenReference(a), Dimension.OpenReference(b)) =>
        Dimension.OpenReference(a max b)
      case (c: Dimension.Constant, _: Dimension.OpenReference) =>
        c
      case ( _: Dimension.OpenReference,c: Dimension.Constant) =>
        c
      case (Dimension.Constant(a), Dimension.Constant(b)) =>
        assert(a == b, "You should trim false faces")
        t
    }

    def restrict(pair: DimensionPair): Dimension = this match {
      case Dimension.OpenReference(id) =>
        if (pair.from.matches(id) || pair.to.matches(id)) {
          pair.from max pair.to
        } else {
          this
        }
      case Dimension.Constant(_) => this
    }
  }

  object Dimension {
    case class OpenReference(id: Long) extends Dimension
    // TODO make it a destructor
    case class Constant(isOne: Boolean) extends Dimension

    val True = Constant(true)
    val False = Constant(false)
  }

  type StuckPos = Value

  sealed trait Whnf extends Value
  // these serve the purpose of recovering syntax
  sealed trait Syntaxial extends Value

  sealed trait HeadCanonical extends Whnf

  sealed trait Stuck extends Whnf

  case class Reference(value: Value, closed: Int) extends Syntaxial
  case class OpenReference(id: Generic, typ: Value) extends Stuck

  case class Universe(level: Int) extends HeadCanonical

  case class Function(domain: Value, codomain: Closure) extends HeadCanonical
  case class Application(lambda: StuckPos, argument: Value) extends Stuck

  // TODO should have a field: recursive, and it must be recursive
  // TODO record should have a type

  case class RecordNode(name: Name, dependencies: Seq[Int], closure: MultiClosure)

  case class Record(level: Int, nodes: Seq[RecordNode]) extends HeadCanonical {
    assert(nodes.isEmpty || nodes.head.dependencies.isEmpty)

    def rthis(r: Reduction): Record = this // Reference(this).deref(r)

    lazy val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[RecordNode], r: Reduction): Value = {
        remaining match {
          case Seq() => Make(known)
          case _ +: tail =>
            Lambda(Closure((p, r) => rec(known :+ p.head, tail, r)))
        }
      }
      rec(Seq.empty, nodes, Reduction.No)
    }

    lazy val makerType: Value = {
      def rec(known: Seq[Value], remaining: Seq[RecordNode], r: Reduction): Value = {
        remaining match {
          case Seq() => rthis(r)
          case Seq(head) =>
            Function(head.closure(head.dependencies.map(known), r),
              Closure((_, r) => rthis(r)))
          case head +: more +: tail =>
            Function(head.closure(head.dependencies.map(known), r), Closure((p, r) => {
              rec(known ++ Seq(p.head), tail, r)
            }))
        }
      }
      rec(Seq.empty, nodes, Reduction.No)
    }
    def projectedType(values: Seq[Value], name: Int, reduction: Reduction /* REDUCTION */): Value = {
      val b = nodes(name)
      b.closure(b.dependencies.map(values), reduction)
    }
  }

  case class Restriction(pair: DimensionPair, body: PathClosure)

  case class Restricted(a: Value, restriction: DimensionPair) extends Syntaxial

  case class Coe(direction: DimensionPair, tp: PathClosure, base: Value) extends Stuck

  case class Hcom(direction: DimensionPair, tp: Value, base: Value, restrictions: Seq[Restriction]) extends Stuck

  case class Make(values: Seq[Value]) extends HeadCanonical

  // it cannot actually stuck. it is a syntaxal value
  case class Maker(value: Value, field: Int) extends Syntaxial

  case class Projection(make: StuckPos, field: Int) extends Stuck

  case class Construct(name: Tag, vs: Seq[Value]) extends HeadCanonical
  // TODO sum should have a type, it can be indexed, so a pi type ends with type_i
  // TODO should have a field: recursive, and it must be recursive, also in case of indexed, use Constructor instead of value
  case class Constructor(name: Tag, parameters: Int, nodes: Seq[MultiClosure]) {
    private[Value] var _sum: Sum = _
    def rthis(r: Reduction): Sum = _sum // Reference(_sum).deref(r)

    lazy val maker: Value = {
      def rec(known: Seq[Value], remaining: Seq[MultiClosure], r: Reduction): Value = {
        remaining match {
          case Seq() => Construct(name, known)
          case _ +: tail =>
            Lambda(Closure((p, r) => rec(known :+ p.head, tail, r)))
        }
      }
      rec(Seq.empty, nodes, Reduction.No)
    }

    lazy val makerType: Value = {
      def rec(known: Seq[Value], remaining: Seq[MultiClosure], r: Reduction): Value = {
        remaining match {
          case Seq() => rthis(r)
          case Seq(head) =>
            Function(head(known, r), Closure((_, r) => rthis(r)))
          case head +: _ +: tail =>
            Function(head(known, r), Closure((p, r) => {
              rec(known :+ p.head, tail, r)
            }))
        }
      }
      rec(Seq.empty, nodes, Reduction.No)
    }
  }

  case class Sum(level: Int, constructors: Seq[Constructor]) extends HeadCanonical {
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
  case class Lambda(closure: Closure) extends HeadCanonical

  case class PatternLambda(id: Generic, typ: Closure, cases: Seq[Case]) extends HeadCanonical

  case class PatternStuck(lambda: PatternLambda, stuck: StuckPos) extends Stuck

  case class Let(var items: Seq[Value], order: Seq[Int], body: Value) extends Syntaxial


  case class PathType(typ: PathClosure, left: Value, right: Value) extends HeadCanonical

  case class PathLambda(body: PathClosure) extends HeadCanonical

  // even when left is a value, it will not stuck, because only open dimension can stuck
  case class PathApplication(left: Value, stuck: Dimension) extends Stuck


  private val gen = new GenericGen.Negative()

  def inferLevel(t1: Value): Int = infer(t1, Reduction.Normalize) match {
    case Universe(l) => l
    case _ => logicError()
  }

  // only works for values of path type and universe types
  def infer(t1: Value, r: Reduction): Value = {
    t1.whnf match {
      case OpenReference(_, v1) =>
        v1
      case Universe(level) => Universe(level + 1)
      case Function(domain, codomain) =>
        (infer(domain, r), infer(codomain(OpenReference(gen(), domain), r), r)) match {
          case (Universe(l1), Universe(l2)) => Universe(l1 max l2)
          case _ => logicError()
        }
      case Record(level, _) =>
        Universe(level)
      case Sum(level, _) =>
        Universe(level)
      case PathType(typ, _, _) =>
        infer(typ.apply(Dimension.OpenReference(gen()), r), r)
      case Application(l1, a1) =>
        infer(l1, r).whnf match {
          case Function(_, c) =>
            c(a1, r)
          case _ => logicError()
        }
      case Projection(m1, f1) =>
        infer(m1, r).whnf match {
          case rr: Record  => rr.projectedType(rr.nodes.indices.map(n => Projection(m1, n)), f1, r)
          case _ => logicError()
        }
      case PatternStuck(l1, s1) =>
        l1.typ(s1, r)
      case PathApplication(l1, d1) =>
        infer(l1, r).whnf match {
          case PathType(typ, _, _) =>
            typ(d1, r)
          case _ => logicError()
        }
      case _ => logicError()
    }
  }



  def extract(pattern: Pattern, v: Value): Option[Seq[Value]] = {
    val vs = mutable.ArrayBuffer[Value]()
    def rec(pattern: Pattern, v: Value): Boolean = {
      pattern match {
        case Pattern.Atom =>
          vs.append(v)
          true
        case Pattern.Make(names) =>
          v.whnf match {
            case Make(values) =>
              names.zip(values).forall(pair => rec(pair._1, pair._2))
            case _ =>
              false
          }
        case Pattern.Construct(name, pt) =>
          v.whnf match {
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

