package mlang.core

import javax.security.auth.login.AppConfigurationEntry.LoginModuleControlFlag
import mlang.name._
import mlang.utils.{DisjointSet, debug, warn}

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

  def from: Value = if (_from == null) this else _from

  /**
    *
    * HOW DOES restrict interacts with Up
    *
    * these two are translated to calls, not Stuck in eval
    *
    * they act structurally on all syntax, and block on all references (closed, generic, meta)
    *
    * so they block on each other, and we will ensure that the canonical block order is Restrict(Up(XxxReference))
    *
    */
  def restrict(a: Seq[DimensionPair]): Value = a.foldLeft(this) {(t, v) => t.restrict(v) }

  def up(b: Int) : Value = this match {
    case Universe(i) =>
      Universe(i + b)
    case Function(domain, im, codomain) =>
      Function(domain.up(b), im, codomain.up(b))
    case Record(level, inductively, ms, ns, nodes) =>
      Record(level + b, inductively.map(_.up(b)), ms, ns, ClosureGraph.up(nodes, b))
    case Make(values) =>
      Make(values.map(_.up(b)))
    case Construct(name, vs) =>
      Construct(name, vs.map(_.up(b)))
    case Sum(level, inductively, constructors) =>
      Sum(level + b, inductively.map(_.up(b)), constructors.map(n => Constructor(n.name, n.ims, ClosureGraph.up(n.nodes, b))))
    case Lambda(closure) =>
      Lambda(closure.up(b))
    case PatternLambda(id, dom, typ, cases) =>
      PatternLambda(id, dom.up(b), typ.up(b), cases.map(a => Case(a.pattern, a.closure.up(b))))
    case PathType(typ, left, right) =>
      PathType(typ.up(b), left.up(b), right.up(b))
    case PathLambda(body) =>
      PathLambda(body.up(b))
    case App(lambda, argument) =>
      App(lambda.up(b), argument.up(b))
    case Coe(direction, tp, base) =>
      Coe(direction, tp.up(b), base.up(b))
    case Hcom(direction, tp, base, faces) =>
      Hcom(direction, tp.up(b), base.up(b), faces.map(_.up(b)))
    case Com(direction, tp, base, faces) =>
      Com(direction, tp.up(b), base.up(b), faces.map(_.up(b)))
    case Maker(value, field) =>
      Maker(value.up(b), field)
    case Projection(make, field) =>
      Projection(make.up(b), field)
    case PatternStuck(lambda, stuck) =>
      PatternStuck(lambda.up(b).asInstanceOf[PatternLambda], stuck.up(b))
    case PathApp(left, stuck) =>
      PathApp(left.up(b), stuck)
    case VType(x, a, p, e) =>
      VType(x, a.up(b), p.up(b), e.up(b))
    case VMake(x, m, n) =>
      VMake(x, m.up(b), n.up(b))
    case VProj(x, m, f) =>
      VProj(x, m.up(b), f.up(b))
    case Let(items, body) =>
      Let(items, body.up(b))
    case Restricted(a, faces) =>
      Restricted(a.up(b), faces)
    case Up(c, d) =>
      if (b + d == 0) c
      else Up(c, b + d)
    case g: Generic =>
      Up(g, b)
    case o: Meta =>
      Up(o, b)
    case o: Reference =>
      Up(o, b)
    case _: Internal =>
      logicError()
  }

  /**
    * this is fsubst, the `a` parameter can only be negative fresh variables, this is safe because we never reuse a
    * negative id.
    */
  def fsubst(a: Long, b: Dimension): Value = this match {
    case Up(term, level) => Up(term.fsubst(a, b), level)
    case Restricted(t, faces) => Restricted(t.fsubst(a, b), faces.map(_.fsubst(a, b)))
    case Maker(value, field) => Maker(value.fsubst(a, b), field)
    case Universe(_) => this
    case Function(domain, impict, codomain) => Function(domain.fsubst(a, b), impict, codomain.fsubst(a, b))
    case Record(level, inductively, names, ims, nodes) => Record(level, inductively, names, ims, ClosureGraph.fsubst(nodes, a, b))
    case Make(values) => Make(values.map(_.fsubst(a, b)))
    case Construct(name, vs) => Construct(name, vs.map(_.fsubst(a, b)))
    case Sum(level, inductively, constructors) => Sum(level, inductively, constructors.map(c => Constructor(c.name, c.ims, ClosureGraph.fsubst(c.nodes, a, b))))
    case Lambda(closure) => Lambda(closure.fsubst(a, b))
    case PatternLambda(id, domain, typ, cases) => PatternLambda(id, domain.fsubst(a, b), typ.fsubst(a, b), cases.map(c => Case(c.pattern, c.closure.fsubst(a, b))))
    case PathType(typ, left, right) => PathType(typ.fsubst(a, b), left.fsubst(a, b), right.fsubst(a, b))
    case PathLambda(body) => PathLambda(body.fsubst(a, b))
    case App(lambda, argument) => App(lambda.fsubst(a, b), argument.fsubst(a, b))
    case Coe(direction, tp, base) => Coe(direction.fsubst(a, b), tp.fsubst(a, b), base.fsubst(a, b))
    case Com(direction, tp, base, faces) => Com(direction.fsubst(a, b), tp.fsubst(a, b), base.fsubst(a, b), Face.fsubst(faces, a, b))
    case Hcom(direction, tp, base, faces) => Hcom(direction.fsubst(a, b), tp.fsubst(a, b), base.fsubst(a, b), Face.fsubst(faces, a, b))
    case Projection(make, field) => Projection(make.fsubst(a, b), field)
    case PatternStuck(lambda, stuck) => PatternStuck(lambda.fsubst(a, b).asInstanceOf[PatternLambda], stuck.fsubst(a, b))
    case PathApp(left, dimension) => PathApp(left.fsubst(a, b), dimension.fsubst(a, b))
    case VProj(x, m, f) => VProj(x.fsubst(a, b), m.fsubst(a, b), f.fsubst(a, b))
    case VType(x, j, k, e) => VType(x.fsubst(a, b), j.fsubst(a, b), k.fsubst(a, b), e.fsubst(a, b))
    case VMake(x, m, n) => VMake(x.fsubst(a, b), m.fsubst(a, b), n.fsubst(a, b))
    case Let(items, body) => Let(items.map(_.fsubst(a, b).asInstanceOf[Reference]), body.fsubst(a, b))
    case r: Reference => r.fsubstSaved(a, b)
    case m@Meta(k) => k match {
      case _: Meta.Closed => m.fsubstSaved(a, b)
      case _: Meta.Open => this // open metas and open references are all in context
    }
    case _: Generic => this
    case _: Internal => logicError()
  }

  // FIXME how does it interact with recursive references?
  def restrict(lv: DimensionPair): Value = if (lv.isTrue) this else this match {
    case u: Universe => u
    case Function(domain, im, codomain) =>
      Function(domain.restrict(lv), im, codomain.restrict(lv))
    case Record(level, inductively, ms, ns, nodes) =>
      Record(level, inductively.map(_.restrict(lv)), ms, ns, ClosureGraph.restrict(nodes, lv))
    case Make(values) =>
      Make(values.map(_.restrict(lv)))
    case Construct(name, vs) =>
      Construct(name, vs.map(_.restrict(lv)))
    case Sum(level, inductively, constructors) =>
      Sum(level, inductively.map(_.restrict(lv)), constructors.map(n => Constructor(n.name, n.ims, ClosureGraph.restrict(n.nodes, lv))))
    case Lambda(closure) =>
      Lambda(closure.restrict(lv))
    case PatternLambda(id, dom, typ, cases) =>
      PatternLambda(id, dom.restrict(lv), typ.restrict(lv), cases.map(a => Case(a.pattern, a.closure.restrict(lv))))
    case PathType(typ, left, right) =>
      PathType(typ.restrict(lv), left.restrict(lv), right.restrict(lv))
    case PathLambda(body) =>
      PathLambda(body.restrict(lv))
    case App(lambda, argument) =>
      App(lambda.restrict(lv), argument.restrict(lv))
    case Coe(direction, tp, base) =>
      Coe(direction.restrict(lv), tp.restrict(lv), base.restrict(lv))
    case Hcom(direction, tp, base, faces) =>
      Hcom(direction.restrict(lv), tp.restrict(lv), base.restrict(lv), Face.restrict(faces, lv))
    case Com(direction, tp, base, faces) =>
      Com(direction.restrict(lv), tp.restrict(lv), base.restrict(lv), Face.restrict(faces, lv))
    case Maker(value, field) =>
      Maker(value.restrict(lv), field)
    case Projection(make, field) =>
      Projection(make.restrict(lv), field)
    case PatternStuck(lambda, stuck) =>
      PatternStuck(lambda.restrict(lv).asInstanceOf[PatternLambda], stuck.restrict(lv))
    case PathApp(left, stuck) =>
      PathApp(left.restrict(lv), stuck.restrict(lv))
    case VType(x, a, p, e) =>
      VType(x.restrict(lv), a.restrict(lv), p.restrict(lv), e.restrict(lv))
    case VMake(x, m, n) =>
      VMake(x.restrict(lv), m.restrict(lv), n.restrict(lv))
    case VProj(x, m, f) =>
      VProj(x.restrict(lv), m.restrict(lv), f.restrict(lv))
    case Let(items, body) =>
      Let(items, body.restrict(lv))
    case Derestricted(v, lv0) =>
      assert(lv == lv0)
      v
    case Up(a, b) =>
      Restricted(Up(a, b), Seq(lv))
    case Restricted(a, faces) =>
      Restricted(a, lv +: faces)
    case g: Generic =>
      Restricted(g, Seq(lv))
    case o: Reference =>
      Restricted(o, Seq(lv))
    case o: Meta =>
      Restricted(o, Seq(lv))
  }

  final override def equals(obj: Any): Boolean = {
    throw new IllegalArgumentException("Values don't have equal. Either call eq or do conversion checking")
  }

  @cached_mutation private var _from: Value = _
  @cached_mutation private var _whnf: Value = _




  // it asserts that if one value cannot be reduced more, it will be eq the original
  def whnf: Value = {
    if (_whnf == null) {
      // TODO can we sort by restriction first?
      def eqFaces(f1: Seq[Face], f2: Seq[Face]): Boolean = f1.eq(f2) || (f1.size == f2.size && f1.zip(f2).forall(p => {
        p._1.restriction.sameRestrict(p._2.restriction) && p._1.body.eq(p._2.body)
      }))
      val candidate = this match {
        case a: HeadCanonical =>
          a
        case r: Reference =>
          r.value.whnf
        case o: Generic =>
          o
        case m: Meta =>
          m.state match {
            case Meta.Closed(v) => v.whnf
            case _: Meta.Open => m
          }
        case Maker(r, i) =>
          r.whnf match {
            case s: Sum => s.constructors(i).maker
            case r: Record =>
              assert(i == -1)
              r.maker
            case _ => logicError() // because we don't accept anoymouns maker expression
          }
        case Let(_, body) =>
          body.whnf
        case App(lambda, argument) =>
          // FIXME we really needs to cleanup these stuff
          def app2(lambda: Value, argument: Value, returns: Value => Value = id): Value = {
            lambda match {
              case Lambda(closure) =>
                returns(closure(argument))
              case p : PatternLambda =>
                split(p, argument.whnf, returns)
              case _ =>
                App(lambda, argument)
            }
          }
          app2(lambda.whnf, argument.whnf, _.whnf) match {
            case App(l2, a2) if lambda.eq(l2) && a2.eq(argument) => this
            case a => a
          }
        case PatternStuck(lambda, stuck) =>
          split(lambda, stuck.whnf, _.whnf) match {
            case PatternStuck(l2, s2) if lambda.eq(l2) && stuck.eq(s2) => this
            case a => a
          }
        case Projection(make, field) =>
          project(make.whnf, field, _.whnf) match {
            case Projection(m2, f2) if make.eq(m2) && field == f2 => this
            case a => a
          }
        case PathApp(left, stuck) =>
          // we MUST perform this, because this doesn't care
          papp(left.whnf, stuck) match {
            case PathApp(l2, s2) if left.eq(l2) && stuck == s2 => this
            case a => a.whnf
          }
        case Coe(direction, tp, base) =>
          // kan ops case analysis on tp, so they perform their own whnf
          coe(direction, tp, base, _.whnf) match {
            case Coe(d2, t2, b2) if d2 == direction && t2.eq(tp) && base.eq(b2) => this
            case a => a
          }
        case Hcom(direction, tp, base, faces) =>
          hcom(direction, tp, base, faces, _.whnf) match {
            case Hcom(d2, t2, b2, f2) if direction == d2 && tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
            case a => a
          }
        case Com(direction, tp, base, faces) =>
          com(direction, tp, base, faces, _.whnf) match {
            case Com(d2, t2, b2, f2) if direction == d2 && tp.eq(t2) && base.eq(b2) && eqFaces(faces, f2) => this
            case a => a
          }
        case VType(x, a, b, _) =>
          x match {
            case _: Dimension.Generic => this
            case Dimension.False => a.whnf
            case Dimension.True => b.whnf
            case _: Dimension.Internal => logicError()
          }
        case VMake(x, m, n) =>
          x match {
            case g: Dimension.Generic => this
            case Dimension.False => m
            case Dimension.True => n
            case _: Dimension.Internal => logicError()
          }
        case VProj(x, m, f) =>
          x match {
            case g: Dimension.Generic =>
              val mw = m.whnf
              @inline def fallback() = if (mw.eq(m)) this else VProj(x, mw, f)
              mw match {
                case VMake(x2, _, n) =>
                  if (x != x2) {
                    warn(s"VProj and VMake has different x?? $x, $x2")
                    fallback()
                  } else {
                    n.whnf
                  }
                case _ => fallback()
              }
            case Dimension.False => app(f, m).whnf
            case Dimension.True => m.whnf
            case _: Dimension.Internal => logicError()
          }
        case Restricted(a, restriction) =>
          val normalized = DimensionPair.normalizeRestriction(restriction)
          if (normalized.isEmpty) {
            a.whnf
          } else {
            a match {
              case GenericOrOpenMeta(it) => Restricted(it, normalized) // stop case
              case u: Up => u.whnf match {
                case Up(GenericOrOpenMeta(it), b) => Restricted(Up(it, b), normalized) // a up's whnf can only block on generics
                case j => j.restrict(normalized).whnf
              }
              case _ => a.restrict(normalized).whnf
            }
          }
        case Up(a, b) =>
          // a can only be reference
          a match {
            case GenericOrOpenMeta(it) => Up(it, b) // stop case
            case ReferenceTail(v, c) => c.map(_.derefUpSaved(b)).getOrElse(v.up(b)).whnf
          }
        case _: Internal =>
          logicError()
      }
      candidate._from = this
      candidate match {
        case Value.OpenMetaHeadedWhnf(_) =>
        case _ =>
          // remember for stable values
          _whnf = candidate
          candidate._whnf = candidate
      }
      candidate
    } else {
      _whnf
    }
  }






  def makerType(i: Int): Value = this.whnf match {
    case s: Sum => s.constructors(i).makerType
    case v: Record => v.makerType
    case _ => logicError()
  }
}


object Value {

  type ClosureGraph = Seq[ClosureGraph.Node]
  object ClosureGraph {
    def fsubst(graph: ClosureGraph, j: Long, k: Dimension): ClosureGraph = {
      graph.map {
        case DependentWithMeta(ds, mc, c) =>
          DependentWithMeta(ds, mc, (a, b) => { val t = c(a, b); (t._1.map(_.fsubst(j, k)), t._2.fsubst(j, k)) })
        case IndependentWithMeta(ds, ms, typ) => IndependentWithMeta(ds, ms.map(_.fsubst(j, k)), typ.fsubst(j, k))
        case _ => logicError()
      }
    }


    def up(graph: ClosureGraph, uu: Int): ClosureGraph = {
      graph.map {
        case DependentWithMeta(ds, mc, c) =>
          DependentWithMeta(ds, mc, (a, b) => { val t = c(a.map(_.up(-uu)), b.map(_.up(-uu))); (t._1.map(_.up(uu)), t._2.up(uu)) })
        case IndependentWithMeta(ds, ms, typ) => IndependentWithMeta(ds, ms.map(_.up(uu)), typ.up(uu))
        case _ => logicError()
      }
    }

    def restrict(graph: ClosureGraph, lv: DimensionPair): ClosureGraph = {
      graph.map {
        case DependentWithMeta(ds, mc, c) =>
          DependentWithMeta(ds, mc, (a, b) => { val t = c(a.map(k => Derestricted(k, lv)), b.map(k => Derestricted(k, lv))); (t._1.map(_.restrict(lv)), t._2.restrict(lv)) })
        case IndependentWithMeta(ds, ms, typ) =>
          IndependentWithMeta(ds, ms.map(_.restrict(lv)), typ.restrict(lv))
        case _ => logicError()
      }
    }



    sealed trait Node {
      def dependencies: Seq[Int]
      def independent: Independent = this.asInstanceOf[Independent]
    }

    sealed trait Dependent extends Node {
    }

    sealed trait Independent extends Node {
      val typ: Value
    }

    private sealed trait Valued extends Independent {
      val value: Value
    }

    private case class DependentWithMeta(dependencies: Seq[Int], metaCount: Int, closure: (Seq[Value], Seq[Value]) => (Seq[Value], Value)) extends Dependent

    private case class IndependentWithMeta(dependencies: Seq[Int], metas: Seq[Value], typ: Value) extends Independent {
    }

    private case class PrivateValuedWithMeta(dependencies: Seq[Int], metas: Seq[Value], typ: Value, value: Value) extends Valued {
    }

    def createMetaAnnotated(nodes: Seq[(Seq[Int], Int, (Seq[Value], Seq[Value]) => (Seq[Value], Value))]): ClosureGraph = {
      nodes.map(a => if (a._1.isEmpty) {
        val t = a._3(Seq.empty, Seq.empty)
        IndependentWithMeta(a._1, t._1, t._2)
      } else {
        DependentWithMeta(a._1, a._2, a._3)
      })
    }

    def get(nodes: ClosureGraph, name: Int, values: Int => Value): Value = {
      var i = 0
      var g = nodes
      while (i < name) {
        g = ClosureGraph.reduce(g, i, values(i))
        i += 1
      }
      g(name).independent.typ
    }


    def reduce(from: ClosureGraph, i: Int, a: Value): ClosureGraph = {
      from(i) match {
        case IndependentWithMeta(ds, mss, typ) =>
          val ns = PrivateValuedWithMeta(ds, mss, typ, a)
          val mms: Seq[Value] = from.flatMap {
            case DependentWithMeta(_, ms, _) => (0 until ms).map(_ => null: Value)
            case IndependentWithMeta(_, ms, _) => ms
            case PrivateValuedWithMeta(_, ms, _, _) => ms
          }
          val vs = from.indices.map(j => if (j == i) a else from(j) match {
            case PrivateValuedWithMeta(_, _, _, v) => v
            case _ => null
          })
          from.map {
            case DependentWithMeta(dss, _, c) if dss.forall(j => vs(j) != null) =>
              val t = c(mms, vs)
              IndependentWithMeta(dss, t._1, t._2)
            case k => k
          }.updated(i, ns)
        case _ => logicError()
      }
    }

    def makerAndType(graph: ClosureGraph, ims: Seq[Boolean], vc: Seq[Value] => Value, tc: Value): (Value, Value) = {
      def rmake(known: Seq[Value]): Value = {
        val size = graph.size - known.size
        size match {
          case 0 => vc(known)
          case _ => Lambda(Closure(p => rmake(known :+ p)))
        }
      }
      def rtyp(index: Int, graph: Seq[ClosureGraph.Node]): Value = {
        val size = graph.size - index
        size match {
          case 0 => tc
          case _ =>
            Function(graph(index).independent.typ, ims(index), Closure(p => {
              val ng = reduce(graph, index, p)
              rtyp(index + 1, ng)
          }))
        }
      }
      val mv = rmake(Seq.empty)
      val mt = rtyp(0, graph)
      (mv, mt)
    }
  }

  def app(lambda: Value, argument: Value, returns: Value => Value = id): Value = {
    lambda match {
      case Lambda(closure) =>
        returns(closure(argument))
      case p : PatternLambda =>
        split(p, argument, returns)
      case _ =>
        App(lambda, argument)
    }
  }

  def split(l: PatternLambda, argument: Value, returns: Value => Value = id): Value = {
    // using first match is even ok for overlapping ones
    var res: Value = null
    var cs = l.cases
    while (cs.nonEmpty && res == null) {
      res = cs.head.tryApp(argument).orNull
      cs = cs.tail
    }
    if (res != null) {
      returns(res)
    } else {
      PatternStuck(l, argument)
    }
  }


  def project(v: Value, name: Int, returns: Value => Value = id): Value = {
    v match {
      case Make(vs) => returns(vs(name))
      case _ => Projection(v, name)
    }
  }

  def papp(l: Value, d: Dimension, returns: Value => Value = id): Value = l match {
    case PathLambda(c) =>
      returns(c(d))
    case a =>
      def constantCase(isOne: Boolean) = {
        infer(a).whnf match {
          case PathType(_, left, right) =>
            returns(if (isOne) right else left)
          case _ => logicError()
        }
      }
      d match {
        case Dimension.True =>
          constantCase(true)
        case Dimension.False =>
          constantCase(false)
        case _: Dimension.Generic =>
          PathApp(l, d)
        case _: Dimension.Internal =>
          logicError()
      }
  }

  def id(v: Value) = v

  private def coe(pair: DimensionPair, typ: AbsClosure, base: Value, returns: Value => Value = id): Value =
    if (pair.isTrue) { // just to base
      returns(base)
    } else {
      val lfresh = dgen()
      val fresh = Dimension.Generic(lfresh)
      typ(fresh).whnf match {
        case Function(domain, _, codomain) =>
          val dabs = AbsClosure(k => domain.fsubst(lfresh, k))
          returns(Lambda(Value.Closure(a => {
            val a_ = Coe(pair.reverse, dabs, a)
            val app_ = App(base, a_)
            Coe(pair,
              AbsClosure(k => codomain.fsubst(lfresh, k)(Coe(DimensionPair(pair.to, k), dabs, a))),
              app_)
          })))
        case r: Record =>
          if (r.nodes.isEmpty) {
            returns(base)
          } else {
            def graph(a: Dimension) = ClosureGraph.fsubst(r.nodes, lfresh, a)
            val closures = mutable.ArrayBuffer[AbsClosure]()
            for (i <- r.nodes.indices) {
              closures.append(
                AbsClosure(dim => {
                  r.nodes(i) match {
                    case _: ClosureGraph.Independent =>
                      Coe(
                        DimensionPair(pair.from, dim),
                        AbsClosure(k => graph(k)(i).independent.typ),
                        Projection(base, i)
                      )
                    case _: ClosureGraph.Dependent =>
                      Coe(
                        DimensionPair(pair.from, dim),
                        AbsClosure(k => ClosureGraph.get(graph(k), i, j => closures(j)(k))),
                        Projection(base, i)
                      )
                  }
                })
              )
            }
            returns(Make(closures.map(_.apply(pair.to))))
          }
        case PathType(typ, left, right) =>
          returns(PathLambda(AbsClosure(dim => {
            Com(
              pair,
              AbsClosure(k => typ.fsubst(lfresh, k)(dim)),
              PathApp(base, dim),
              Seq(
                { val dp = DimensionPair(dim, Dimension.False); Face(dp, AbsClosure(a => left.fsubst(lfresh, a).restrict(dp))) },
                { val dp = DimensionPair(dim, Dimension.True); Face(dp,AbsClosure(a => right.fsubst(lfresh, a).restrict(dp))) }
                  ))
          })))
        case _: Sum =>
          ???
        case VType(x, a, b, e) =>
          val r = pair.from
          val r_ = pair.to
          val aabs = AbsClosure(s => a.fsubst(lfresh, s))
          val babs = AbsClosure(s => b.fsubst(lfresh, s))
          returns(if (x != fresh) { // in this case we can use `map` on `typ`
            VMake(x,
              Coe(pair, aabs, base).restrict(DimensionPair(x, Dimension.False)),
              Com(pair,
                babs,
                VProj(x, base, Projection(e.fsubst(lfresh, r), 0)),// this is ok because we know M is of this type!!
                Seq(
                  { val dp = DimensionPair(x, Dimension.False);
                    Face(dp, AbsClosure(y => App(
                      Projection(e.fsubst(lfresh, y), 0),
                      Coe(DimensionPair(r, y), aabs, base)).restrict(dp))) },
                  { val dp = DimensionPair(x, Dimension.True);
                    Face(dp, AbsClosure(y =>
                      Coe(DimensionPair(r, y), babs, base).restrict(dp))) },
                )))
          } else {
            def basep(src: Dimension, dest: Dimension) = {
              Coe(DimensionPair(src, dest), babs, VProj(src, base, Projection(e.fsubst(lfresh, src), 0)))
            }
            ???
          })
        case _ =>
          Coe(pair, typ, base)
      }
    }

  private def com(pair: DimensionPair, typ: AbsClosure, base: Value, restriction0: Seq[Face], returns: Value => Value = id): Value = {
    // do we need to implement the extra shortcuts?
    returns(Hcom(
      pair,
      typ(pair.to),
      Coe(pair, typ, base),
      restriction0.map(n => Face(n.restriction, n.body.mapd((j, d) => Coe(DimensionPair(d, pair.to), typ, j))))))
  }

  private def hcom(pair: DimensionPair, typ: Value, base: Value, restriction0: Seq[Face], returns: Value => Value = id): Value = {
    val rs0 = restriction0.filter(!_.restriction.isFalse)
    val rs = if (rs0.size == restriction0.size) restriction0 else rs0
    if (pair.isTrue) {
      returns(base)
    } else {
      rs.find(a => a.restriction.isTrue) match { // always true face
        case Some(n) =>
          returns(n.body(pair.to))
        case None =>
          val typw = typ.whnf
          typw match {
            case Function(_, _, codomain) => returns(Lambda(Value.Closure(a =>
              Hcom(pair, codomain(a), App(base, a), rs.map(n => Face(n.restriction, n.body.map(j => App(j, a.restrict(n.restriction))))))
            )))
            case r: Record =>
              val graph = r.nodes
              if (graph.isEmpty) {
                returns(base)
              } else {
                val closures = mutable.ArrayBuffer[AbsClosure]()
                for (i <- graph.indices) {
                  closures.append(
                    AbsClosure(dim => {
                      graph(i) match {
                        case in: ClosureGraph.Independent =>
                          Hcom(
                            DimensionPair(pair.from, dim),
                            in.typ,
                            Projection(base, i),
                            rs.map(n => Face(n.restriction, n.body.map(j => Projection(j, i))))
                          )
                        case _: ClosureGraph.Dependent =>
                          Com(
                            DimensionPair(pair.from, dim),
                            AbsClosure(k => ClosureGraph.get(graph, i, j => closures(j)(k))),
                            Projection(base, i),
                            rs.map(n => Face(n.restriction, n.body.map(j => Projection(j, i))))
                          )
                      }
                    })
                  )
                }
                returns(Make(closures.map(_.apply(pair.to))))
              }
            case PathType(ty, left, right) =>
              returns(PathLambda(AbsClosure(dim => {
                Hcom(
                  pair,
                  ty(dim),
                  PathApp(base, dim),
                  Seq(
                    { val dp = DimensionPair(dim, Dimension.False); Face(dp, AbsClosure(left.restrict(dp))) },
                    { val dp = DimensionPair(dim, Dimension.True); Face(dp, AbsClosure(right.restrict(dp))) },
                  ) ++ rs.map(n => Face(n.restriction, n.body.map(j => PathApp(j, dim.restrict(n.restriction))))))
              })))
            case Sum(l, inductively, c) =>
              ???
            case VType(x, a, b, e) =>
              val x0 = DimensionPair(x, Dimension.False)
              val O = AbsClosure(y => Hcom(DimensionPair(pair.from, y).restrict(x0), a /* no need */, base.restrict(x0), Face.restrict(rs, x0)))
              returns(
                VMake(
                  x, O(pair.to), Hcom(pair, b, VProj(x, base, Projection(e, 0)),
                    Seq(
                      Face(x0, AbsClosure(y => App(Projection(e, 0), O(y)))),
                      // FIXME it seems redtt doesn't have this face, the face0 is used to satisfy the equality rule for VMake, so face1 seems not useful?
                      // Face(DimensionPair(x, Dimension.True), AbsClosure(y => Hcom(DimensionPair(pair.from, y), b, base, rs))),
                    ) ++ rs.map(n => Face(n.restriction, n.body.map(j => VProj(x.restrict(n.restriction), j, Projection(e.restrict(n.restriction), 0)))))))
              )
            case _ =>
              Hcom(pair, typw, base, rs)
          }
      }
    }
  }



  implicit class MultiClosure(private val func: Seq[Value] => Value) extends AnyVal {
    def eq(b: MultiClosure): Boolean = func.eq(b.func)
    def apply() = func(Seq.empty)
    def apply(seq: Seq[Value]): Value = func(seq)
    def fsubst(a: Long, b: Dimension): MultiClosure = MultiClosure(v => this(v).fsubst(a, b))
    def restrict(lv: DimensionPair): MultiClosure = MultiClosure(v => this(v.map(a => Derestricted(a, lv))).restrict(lv))
    def up(b: Int): MultiClosure = MultiClosure(v => this(v.map(_.up(-b))).up(b))
  }

  implicit class Closure(private val func: Value => Value) extends AnyVal {

    def eq(b: Closure): Boolean = func.eq(b.func)
    def apply(seq: Value): Value = func(seq)
    def fsubst(a: Long, b: Dimension): Closure = Closure(v => this(v).fsubst(a, b))
    def restrict(lv: DimensionPair): Closure = Closure(v => this(Derestricted(v, lv)).restrict(lv))
    def up(b: Int): Value.Closure = Closure(v => this(v.up(-b)).up(b))
  }

  object Closure {
    def apply(a: Value): Closure = Closure(_ => a)
  }

  object AbsClosure {
    def apply(a: Value): AbsClosure = AbsClosure(_ => a)
    type StuckPos = AbsClosure
  }

  implicit class AbsClosure(private val func: Dimension => Value) extends AnyVal {
    def eq(b: AbsClosure): Boolean = func.eq(b.func)
    def apply(seq: Dimension): Value = func(seq)
    def mapd(a: (Value, Dimension) => Value): AbsClosure = AbsClosure(d => a(this(d), d))
    def map(a: Value => Value): AbsClosure = AbsClosure(d => a(this(d)))
    def fsubst(a: Long, b: Dimension): AbsClosure = AbsClosure(v => this(v).fsubst(a, b))
    def restrict(lv: DimensionPair): AbsClosure = AbsClosure(v => this(Dimension.Derestricted(v, lv)).restrict(lv))
    def up(b: Int): AbsClosure = AbsClosure(v => this(v).up(b))
  }

  object DimensionPair {
    def checkValidRestrictions(ds0: Seq[DimensionPair]): Boolean = {
      // TODO this is an extension for validity now, we don't make a difference between i=j and j=i
      val ds = ds0.map(_.sorted)
      ds.exists(a => a.isTrue) || ds.flatMap(r => ds.map(d => (r, d))).exists(p => {
        p._1.from == p._2.from && !p._1.from.isConstant &&
            p._1.to.isConstant && p._2.to.isConstant && p._1.to != p._2.to
      })
    }

    def normalizeRestriction(pairs: Seq[DimensionPair]): Seq[DimensionPair] = {
      val a = DisjointSet[Dimension]()
      for (p <- pairs) {
        if (!a.contains(p.from)) a += p.from
        if (!a.contains(p.to)) a += p.to
        a.union(p.from, p.to)
      }
      val seq = a.sets.map(_.toSeq).filter(_.size <= 1).toSeq
          .map(_.sortWith((a, b) => (a max b) == b))
          .sortWith((a, b) => (a.last max b.last) == b.last)
      if (debug.enabled) assert(!seq.exists(_.endsWith(Seq(Dimension.False, Dimension.True))))
      seq.flatMap(a => a.dropRight(1).map(b => DimensionPair(b, a.last)))
    }

    def sameRestrict(p: Seq[DimensionPair], r: Seq[DimensionPair]): Boolean = {
      normalizeRestriction(p) == normalizeRestriction(r)
    }
  }

  case class DimensionPair(from: Dimension, to: Dimension) {
    def fsubst(a: Long, b: Dimension) = DimensionPair(from.fsubst(a, b), to.fsubst(a, b))

    def restrict(a: DimensionPair) = DimensionPair(from.restrict(a), to.restrict(a))

    def sameRestrict(p: DimensionPair): Boolean = this.sorted == p.sorted

    def reverse: DimensionPair = DimensionPair(to, from)

    def isFalse: Boolean = (from == Dimension.False && to == Dimension.True) || (from == Dimension.True && to == Dimension.False)

    def isTrue: Boolean = from == to

    def sorted: DimensionPair = if ((to max from) == to) this else DimensionPair(to, from)
  }

  sealed trait Dimension extends {
    def fsubst(a: Long, b: Dimension): Dimension = if (matches(a)) b else this

    def matches(id: Long): Boolean = this match {
      case Dimension.Generic(iid) => iid == id
      case _ => false
    }

    def isConstant: Boolean = this match {
      case Dimension.Generic(_) => false
      case _ => true
    }

    def min(t: Dimension): Dimension = if ((this max t) == t) this else t

    def max(t: Dimension): Dimension = (this, t) match {
      case (Dimension.Generic(a), Dimension.Generic(b)) =>
        Dimension.Generic(a max b)
      case (c, _: Dimension.Generic) =>
        c
      case (_: Dimension.Generic, c) =>
        c
      case (Dimension.True, _) =>
        Dimension.True
      case (_, Dimension.True) =>
        Dimension.True
      case _ =>
        Dimension.False
    }


    def restrict(seq: Seq[DimensionPair]): Dimension = seq.foldLeft(this) { (t, v) => t.restrict(v) }


    def restrict(pair: DimensionPair): Dimension = this match {
      case Dimension.Derestricted(d, pair2) =>
        assert(pair2 == pair)
        d
      case Dimension.Generic(id) =>
        if (pair.from.matches(id) || pair.to.matches(id)) {
          pair.from max pair.to
        } else {
          this
        }
      case _ => this
    }
  }

  object Dimension {
    sealed trait Internal extends Dimension
    case class Generic(id: Long) extends Dimension
    private[Value] case class Derestricted(a: Dimension, lv: DimensionPair) extends Internal

    object True extends Dimension
    object False extends Dimension
  }

  type StuckPos = Value
  // these serve the purpose of recovering syntax
  sealed trait Syntaxial extends Value
  sealed trait Internal extends Value
  sealed trait Whnf extends Value
  sealed trait HeadCanonical extends Whnf
  sealed trait Stuck extends Whnf
  sealed trait CubicalUnstable extends Whnf // this value can reduce more, but only when restricted


  object Meta {
    sealed trait State

    case class Closed(v: Value) extends State
    case class Open(id: Long, typ: Value) extends State
  }
  case class Meta(@polarized_mutation var state: Meta.State) extends Syntaxial {
    def solved: Value = state.asInstanceOf[Meta.Closed].v
    def isSolved: Boolean = state.isInstanceOf[Meta.Closed]

    @cached_mutation private val _fsubsts = mutable.HashMap.empty[(Long, Dimension), Meta]
    def fsubstSaved(a: Long, b: Dimension): Meta = {
      if (!_fsubsts.contains((a, b))) {
        val r = Meta(null)
        _fsubsts.put((a, b), r)
        r.state = Meta.Closed(state.asInstanceOf[Meta.Closed].v.fsubst(a, b))
      }
      _fsubsts((a, b))
    }
  }

  case class Reference(@lateinit private var value000: Value) extends Syntaxial {



    def value: Value =  value000
    def value_=(v: Value): Unit = {
      _ups.clear()
      _fsubsts.clear()
      value000 = v
    }

    @cached_mutation private val _ups = mutable.ArrayBuffer.empty[Value]
    def derefUpSaved(b: Int): Value = {
      if (b < _ups.size && _ups(b) != null) {
        _ups(b)
      } else {
        val v = value.up(b)
        while (b >= _ups.size) _ups.append(null)
        _ups.update(b, v)
        v
      }
    }

    @cached_mutation private val _fsubsts = mutable.HashMap.empty[(Long, Dimension), Reference]
    def fsubstSaved(a: Long, b: Dimension): Reference = {
      if (!_fsubsts.contains((a, b))) {
        val r = Reference(null)
        _fsubsts.put((a, b), r)
        r.value000 = this.fsubst(a, b)
      }
      _fsubsts((a, b))
    }

    override def toString: String = "Reference"
  }

  object ReferenceTail {
    def rec(a: Value, ref: Option[Reference]): Option[(Value, Option[Reference])] = a match {
      case Meta(Meta.Closed(v)) => rec(v, ref)
      case r@Reference(t) => rec(t, Some(r))
      case els => Some((els, ref))
    }
    def unapply(a: Value): Option[(Value, Option[Reference])] = rec(a, None)
  }
  object GenericOrOpenMeta {
    def unapply(a: Value): Option[Value] = a match {
      case g: Generic => Some(g)
      case Meta(m: Meta.Open) => Some(a)
      case _ => None
    }
  }

  case class Generic(id: Long, @lateinit var typ: Value) extends Stuck

  case class Universe(level: Int) extends HeadCanonical

  object Universe {
    def suc(i: Int) = Universe(i + 1)
    def level0 = Universe(1)
    def level1 = Universe(1)
  }

  case class Up(term: Value, level: Int) extends Syntaxial

  case class Function(domain: Value, impict: Boolean, codomain: Closure) extends HeadCanonical
  case class App(lambda: StuckPos, argument: Value) extends Stuck

  case class Inductively(id: Long) {

    def up(b: Int): Inductively = this
    def restrict(lv: DimensionPair): Inductively = this
  }

  case class Record(
      level: Int,
      inductively: Option[Inductively],
      names: Seq[Name],
      ims: Seq[Boolean],
      nodes: ClosureGraph) extends HeadCanonical {
    assert(names.size == nodes.size)

    private def rthis(): Value = Reference(this)

    private lazy val makerAndType: (Value, Value) = ClosureGraph.makerAndType(nodes, ims, vs => Make(vs), rthis())
    lazy val maker: Value = makerAndType._1
    lazy val makerType: Value = makerAndType._2

    def projectedType(values: Value, name: Int): Value = {
      ClosureGraph.get(nodes, name, i => Projection(values, i))
    }
  }

  object Face {
    def fsubst(faces: Seq[Face], a: Long, b: Dimension): Seq[Face] = {
      faces.flatMap(n => {
        val r = n.restriction.fsubst(a, b)
        if (r.isFalse) {
          None
        } else {
          Some(Face(r, n.body.fsubst(a, b)))
        }
      })
    }

    def restrict(faces: Seq[Face], lv: DimensionPair): Seq[Face] = {
      faces.flatMap(n => {
        val r = n.restriction.restrict(lv)
        if (r.isFalse) {
          None
        } else {
          Some(Face(r, n.body.restrict(lv)))
        }
      })
    }
  }
  case class Face(restriction: DimensionPair, body: AbsClosure) {
    def restrict(a: DimensionPair) = Face(restriction.restrict(a), body.restrict(a))
    def up(a: Int) = Face(restriction, body.up(a))
  }


  case class Restricted(a: Value, faces: Seq[DimensionPair]) extends Syntaxial
  private case class Derestricted(a: Value, lv: DimensionPair) extends Internal

  case class Coe(direction: DimensionPair, tp: AbsClosure.StuckPos, base: Value) extends Stuck

  case class Com(direction: DimensionPair, tp: AbsClosure.StuckPos, base: Value, faces: Seq[Face]) extends Stuck

  case class Hcom(direction: DimensionPair, tp: StuckPos, base: Value, faces: Seq[Face]) extends Stuck

  case class Make(values: Seq[Value]) extends HeadCanonical

  // it cannot actually stuck. it is a syntaxal value
  case class Maker(value: Value, field: Int) extends Syntaxial

  case class Projection(make: StuckPos, field: Int) extends Stuck

  case class Construct(name: Int, vs: Seq[Value]) extends HeadCanonical
  case class Constructor(name: Name, ims: Seq[Boolean], nodes: ClosureGraph) {
    private[Value] var _sum: Sum = _
    private def rthis(): Value = Reference(_sum)

    private def index = _sum.constructors.indexWhere(_.eq(this))

    private lazy val makerAndType: (Value, Value) = ClosureGraph.makerAndType(nodes, ims, vs => Construct(index, vs), rthis())
    lazy val maker: Value = makerAndType._1
    lazy val makerType: Value = makerAndType._2
  }


  case class Sum(
      level: Int,
      inductively: Option[Inductively],
      constructors: Seq[Constructor]) extends HeadCanonical {
    for (c <- constructors) {
      c._sum = this
    }
  }

  case class Case(pattern: Pattern, closure: MultiClosure) {
    def tryApp(v: Value): Option[Value] = {
      extract(pattern, v).map(a => closure(a))
    }
  }

  /**
    * this lambda is returnsparent on the arguments
    */
  case class Lambda(closure: Closure) extends HeadCanonical

  // FIXME seems we must have domain here?
  case class PatternLambda(id: Long, domain: Value, typ: Closure, cases: Seq[Case]) extends HeadCanonical

  case class PatternStuck(lambda: PatternLambda, stuck: StuckPos) extends Stuck

  case class Let(items: Seq[Reference], body: Value) extends Syntaxial


  case class PathType(typ: AbsClosure, left: Value, right: Value) extends HeadCanonical

  case class PathLambda(body: AbsClosure) extends HeadCanonical

  // the left and right BOTH stuck
  case class PathApp(left: StuckPos, dimension: Dimension) extends Stuck

  case class VType(x: Value.Dimension, a: Value, b: Value, e: Value) extends CubicalUnstable
  case class VMake(x: Value.Dimension, m: Value, n: Value) extends CubicalUnstable
  case class VProj(x: Value.Dimension, m: StuckPos, f: Value) extends Stuck

  // these values will not be visible to users! also I guess it is ok to be static, it will not overflow right?
  private val gen = LongGen.Negative.gen
  private val dgen = LongGen.Negative.dgen

  def inferLevel(t1: Value): Int = infer(t1) match {
    case Universe(l) => l
    case _ => logicError()
  }

  // it is like in type directed conversion checking, this works because we always call infer on whnf, so neutural values
  // can infer it's type
  def infer(t1: Value): Value = {
    t1.whnf match {
      case g: Generic =>
        g.typ
      case Restricted(a, fs) =>
        fs.foldLeft(infer(a)) { (t, r) => t.restrict(r) }
      case Universe(level) => Universe.suc(level)
      case Up(a, b) => infer(a).up(b)
      case Function(domain, _, codomain) =>
        (infer(domain), infer(codomain(Generic(gen(), domain)))) match {
          case (Universe(l1), Universe(l2)) => Universe(l1 max l2)
          case _ => logicError()
        }
      case r: Record =>
        Universe(r.level)
      case s: Sum =>
        Universe(s.level)
      case PathType(typ, _, _) =>
        infer(typ.apply(Dimension.Generic(dgen())))
      case App(l1, a1) =>
        infer(l1).whnf match {
          case Function(_, _, c) =>
            c(a1)
          case _ => logicError()
        }
      case Projection(m1, f1) =>
        infer(m1).whnf match {
          case rr: Record  => rr.projectedType(m1, f1)
          case _ => logicError()
        }
      case PatternStuck(l1, s1) =>
        l1.typ(s1)
      case PathApp(l1, d1) =>
        infer(l1).whnf match {
          case PathType(typ, _, _) => typ(d1)
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

  object OpenMetaHeadedWhnf {

    def unapply(value: Value): Option[Meta] = {
      value match {
        case _: HeadCanonical => None
        case _: CubicalUnstable => None
        case _: Generic => None
        case o: Meta => Some(o)
        case App(lambda, _) => unapply(lambda)
        case Projection(make, _) => unapply(make)
        case PatternStuck(_, stuck) => unapply(stuck)
        case PathApp(left, _) => unapply(left)
        case VProj(_, m, _) => unapply(m)
        case Coe(_, typ, _) =>
          // FIXME this rule is really wired...
          unapply(typ(Dimension.Generic(dgen())).whnf)
        case Hcom(_, tp, _, _) => unapply(tp)
        case Restricted(a, _) => unapply(a)
        case _: Com => logicError()
        case _: Syntaxial => logicError()
        case _: Internal => logicError()
      }
    }
  }
}

