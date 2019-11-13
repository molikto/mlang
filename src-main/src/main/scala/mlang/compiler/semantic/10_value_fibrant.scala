package mlang.compiler.semantic

import Value._
import mlang.compiler.GenLong.Negative.{dgen, gen}
import scala.collection.mutable
import mlang.utils._

val HCOMP_UNIVERSE = false


// currently put in a object, becasue this enables us to debug these
object ValueFibrant {
  def transpBody(t: Transp): Value = t match {
    case Transp(tp, phi, base) =>
      if (phi.nfTrue) {
        base.whnf
      } else {
        val dim = Formula.Generic(dgen())
        val unreduced = tp.apply(dim)
        val reduced = unreduced.whnf
        reduced match {
          case _: Function =>
            inline def tpr(i: Formula) = tp(i).whnf.asInstanceOf[Function]
            Lambda(Closure(v => {
              inline def w(i: Formula) = transpFill_inv(i, phi, AbsClosure(a => tpr(a).domain), v)
              val w0 = transp_inv(phi, AbsClosure(a => tpr(a).domain), v)
              Transp(AbsClosure(i => tpr(i).codomain(w(i))), phi, App(base, w0))
            }))
          case _: PathType =>
            inline def tpr(i: Formula) = tp(i).whnf.asInstanceOf[PathType]
            PathLambda(AbsClosure(dim => {
              Comp(
                AbsClosure(i => tpr(i).typ(dim)),
                PathApp(base, dim),
                Seq(
                  (phi, AbsClosure(_ => PathApp(base, dim))),
                  (Formula.Neg(dim), AbsClosure(a => tpr(a).left)),
                  (dim, AbsClosure(a => tpr(a).right))
                ).toMap)
            }))
          case r: Record =>
            if (r.nodes.isEmpty) {
              base.whnf
            } else {
              val closures = transpFill(r.nodes, i => tp(i).whnf.asInstanceOf[Record].nodes, phi, i => Projection(base, i))
              Make(closures.map(_.apply(Formula.True)))
            }
          case s: Sum =>
            if (s.noArgs) {
              base.whnf
            } else {
              base.whnf match {
                case Construct(c, vs, rs, d) =>
                  inline def tpr(i: Formula) = tp(i).whnf.asInstanceOf[Sum].constructors(c)
                  val cc = s.constructors(c)
                  val theta = transpFill(cc.nodes, i => tpr(i).nodes, phi, vs)
                  val tele = theta.map(_.apply(Formula.True))
                  val res = if (rs.isEmpty) {
                    Construct(c, tele, rs, d)
                  } else {
                    // rules from the HIT paper
                    // val w1p = Construct(c, tele, rs, d)
                    // val item1 = (phi, AbsClosure(_ => base))
                    // def alpha(e: AbsClosure) = squeeze(tp, e, phi)
                    // val items = cc.nodes.reduce(rs).phi().toSeq.map(f => {
                    //   val e = AbsClosure(i => tpr(i).nodes.reduceAll(theta.map(_.apply(i))).reduce(rs).restrictions().find(_._1 == f).get._2())
                    //   val abs = AbsClosure(i => alpha(e)(Formula.Neg(i)))
                    //   (f, abs)
                    // }).toMap.updated(item1._1, item1._2)
                    // Hcomp(tp(Formula.True), w1p, items)
                    // with this rule changed, it goes from ~10s to , both without hcomp_universe
                    Construct(c, tele, rs, tp(Formula.True).whnf.asInstanceOf[Sum].constructors(c).nodes.reduceAll(tele).reduce(rs).restrictions())
                  }
                  res.whnf
                case Hcomp(hty, hbase, faces) =>
                  val res = Hcomp(tp(Formula.True), Transp(tp, phi, hbase), faces.map(pr => (pr._1, pr._2.map(v => Transp(tp, phi, v)))))
                  res.whnf
                case _: StableCanonical => logicError()
                case a => if (a == base) t else Transp(tp, phi, a)
              }
            }
          case g: GlueType =>
            transpGlue(g, dim, phi, base).whnf
          case Hcomp(Universe(_), b0, faces) =>
            println("transp hcomp universe")
            if (HCOMP_UNIVERSE) transpHcompUniverse(b0, faces, dim, phi, base).whnf
            else logicError()
          case _: Universe =>
            base
          case other =>
            t
        }
      }
  }

  def hcompBody(t: Hcomp): Value = t match {
    case Hcomp(tp, base, faces) =>
        faces.find(_._1.nfTrue) match {
          case Some(t) => t._2(Formula.True)
          case None =>
            val tp0 = tp.whnf
            tp0 match {
              case PathType(a, u, w) =>
                PathLambda(AbsClosure(j => Hcomp(
                  a(j),
                  PathApp(base, j),
                  faces.view.mapValues(_.map(v => PathApp(v, j))).toMap
                    .updated(Formula.Neg(j), AbsClosure(_ => u))
                    .updated(j, AbsClosure(_ => w))
                )))
              case Function(_, _, b) =>
                Lambda(Closure(v => Hcomp( b(v), App(base, v), faces.view.mapValues(_.map(j => App(j, v))).toMap)))
              case Record(_, _, cs) =>
                Make(hcompGraph(cs, faces, base, (v, i) => Projection(v, i)))
              case s@Sum(i, hit, cs) =>
                if (!hit) {
                  base.whnf match {
                    case cc@SimpleConstruct(c, vs) =>
                      if (s.noArgs) { // FIXME this doesn't seems to be correct!!! how to judge if the term is open or not
                        base
                      } else {
                        SimpleConstruct(c, hcompGraph(cs(c).nodes, faces, cc, (b, i) => b.whnf.asInstanceOf[SimpleConstruct].vs(i)))
                      }
                    case _: StableCanonical => logicError()
                    case a => if (a == base && s == tp) t else Hcomp(s, a, faces)
                  }
                } else {
                  val a = base.whnf
                  if (a == base && s == tp) t else Hcomp(s, a, faces)
                }
              case u: Universe =>
                if (HCOMP_UNIVERSE) {
                  if (u == tp) t else Hcomp(u, base, faces)
                } else {
                  GlueType(base, faces.view.mapValues({ f =>
                    val A = f(Formula.False)
                    val B = f(Formula.True)
                    () => Make(Seq(B, apps(BuiltIn.path_to_equiv, Seq(B, A, PathLambda(AbsClosure(a => f(Formula.Neg(a))))))))
                  }).toMap)
                }
              case Hcomp(u: Universe, b, es) =>
                println("hcomp hcomp universe")
                if (HCOMP_UNIVERSE) hcompHcompUniverse(b, es, base, faces)
                else logicError()
              case g: GlueType =>
                hcompGlue(g, base, faces)
              case a => if (a == tp) t else Hcomp(a, base, faces)
            }
        }
  }

  def transpHcompUniverse(A: Value, es: AbsClosureSystem, dim: Formula.Generic, si: Formula, u0: Value): Value = {
    // this mapping is done in hcomp in cubicaltt
    val A0 = A.fswap(dim.id, Formula.False)
    val A1 = A.fswap(dim.id, Formula.True)
    val es0 = es.fswap(dim.id, Formula.False)
    val es1 = es.fswap(dim.id, Formula.True)

    if (NORMAL_FORM_MODEL) println("unglue created transp hcomp 1")
    // this is UnglueU in cubicaltt, the es0 is a system of path lambdas
    if (u0.isInstanceOf[Transp] && !u0.whnf.isInstanceOf[Glue] && !es0.contains(Formula.True)) {
      val a = 1
    }
    val v0 = Unglue(A0, u0, true, es0.view.mapValues(a => () => PathLambda(a)).toMap)

    val faces_elim_dim = es.toSeq.map(a => (a._1.elim(dim.id), a._2)).filter(!_._1.nfFalse).toMap
    val t1s = faces_elim_dim.view.mapValues(p => {
      val tp = p(Formula.True)
      Transp(AbsClosure(i => tp.fswap(dim.id, i)), si, u0)
    }).toMap
    val v1 = gcomp(AbsClosure(i => A.fswap(dim.id, i)), v0,
      faces_elim_dim.map((pair: (Formula, AbsClosure)) => {
        val els = pair._2
        val abs = AbsClosure(i => { // this i binds in the system
          transp_inv(Formula.False, els.fswap(dim.id, i),
            transpFill(i, si, AbsClosure(i => els(Formula.True).fswap(dim.id, i)), u0)
          )
        })
        (pair._1, abs)
      }).updated(si, AbsClosure(_ => v0)))
    val sys = t1s.updated(si, u0).filterKeys(!_.nfFalse)
    val fibersys_ = es1.map((pair: (Formula, AbsClosure)) => {
      val eq = pair._2
      val b = v1
      val as = sys
      val dg = Formula.Generic(dgen())
      val unreduced = eq(dg)
      val res = unreduced.whnf match {
        case s: Sum if s.noArgs =>
          // because we know this is non-dependent
          val p1 = () => Hcomp(unreduced, b,  as.view.mapValues(a => AbsClosure(_ => a)).toMap)
          val p2 = hfill(unreduced, b,  as.view.mapValues(a => AbsClosure(_ => a)).toMap)
          (p1, p2: AbsClosure)
        case _ =>
          val adwns = as.map((pair: (Formula, Value)) => {
            val fs = pair._1
            val els = pair._2
            (fs, AbsClosure(j => {
              transpFill_inv(j, Formula.False, eq, els)}))
          }).toMap
          val left = fill(eq, b, adwns)
          val a = comp(eq, b, adwns)
          val right = AbsClosure(j =>
            transpFill_inv(j, Formula.False, eq, a)
          )
          val p = AbsClosure(i => {
            comp(AbsClosure(a => eq(Formula.Neg(a))), a,
              adwns.updated(Formula.Neg(i), left).updated(i, right).view.mapValues(v => AbsClosure(j => v(Formula.Neg(j)))).toMap
            )
          })
          (() => a, p: AbsClosure)
      }
      (pair._1, res)
    }).toMap
    val t1s_ = fibersys_.view.mapValues(_._1).toMap
    val v1_ = Hcomp(A1, v1, fibersys_.view.mapValues(_._2).toMap.updated(si, AbsClosure(_ => v1)))
    Glue(v1_, t1s_)
  }

  def hcompHcompUniverse(b: Value, es: AbsClosureSystem, u: Value, us: AbsClosureSystem): Value = {
    val wts = es.map((pair: (Formula, AbsClosure)) => {
      val eal = pair._2
      (pair._1, AbsClosure(i =>
        transp_inv(Formula.False, eal, hfill(eal( Formula.True), u, us).apply(i))
      ))
    })
    val t1s = es.map((pair: (Formula, AbsClosure)) => {
      val els = pair._2
      (pair._1, () => Hcomp(els(Formula.True), u, us))
    })
    val esmap = es.view.mapValues(a => () => PathLambda(a)).toMap
      if (NORMAL_FORM_MODEL) println("unglue created hcomp hcomp 1")
    val v = Unglue(b, u, true, esmap)
    val vs = us.map((pair: (Formula, AbsClosure)) => {
      (pair._1, pair._2.map(v => {
        if (NORMAL_FORM_MODEL) println("unglue created hcomp hcomp 2")
        Unglue(b, v, true, esmap)
      }))
    })
    val v1 = Hcomp(b, v, vs ++ wts)
    Glue(v1, t1s)
  }

  def transpGlue(B: GlueType, dim: Formula.Generic, si: Formula, u0: Value): Value = {
    def B_swap(f: Formula) = B.fswap(dim.id, f).asInstanceOf[GlueType]
    val B0 = B_swap(Formula.False)
    def A_swap(i: Formula) = B.ty.fswap(dim.id, i)
    val B1 = B_swap(Formula.True)
    val A1 = B1.ty
    val A0 = B0.ty
    // a0: A(i/0)
    if (NORMAL_FORM_MODEL) println("unglue created transp glue 1")
    val a0 = Unglue(A0, u0, false, B0.faces)
    // defined in phi_elim_i
    def t_tide(trueFace: Value, i: Formula) = {
      transpFill(i, si, AbsClosure(i => {
      Projection(trueFace.fswap(dim.id, i), 0)
      }), u0)
    }
    val faces_elim_dim = B.faces.toSeq.map(a => (a._1.elim(dim.id), a._2)).filter(!_._1.nfFalse).toMap
    val B1_faces = B1.faces.filter(_._1.normalForm != NormalForm.False)
    def t1(trueFace: Value) = t_tide(trueFace, Formula.True)
    // a1: A(i/1) and is defined on both si and elim(i, phi)
    val a1 = gcomp(
      AbsClosure(i => A_swap(i)),
      a0,
      faces_elim_dim.view.mapValues(tf => {
        AbsClosure(i => {
          val tf0 = tf()
          val EQi  = tf0.fswap(dim.id, i)
          val w = Projection(EQi, 1)
          App(Projection(w, 0), t_tide(tf0, i))
        })
      }).toMap.updated(si, AbsClosure(_ => a0))
    )
    // ..., phi(i/1) |- (t1`, alpha) // true face must have (i/1)
    def pair(trueFace: Value) = {
      val w = Projection(trueFace, 1)
      val compo = App(Projection(w, 1), a1) // is_contr(fiber_at(w(i/1).1, a1))
      ghcomp(apps(BuiltIn.fiber_at, Seq(Projection(trueFace, 0), A1, Projection(w, 0), a1)), Projection(compo, 0),
        faces_elim_dim.view.mapValues(tf => {
          AbsClosure(i => {
            val u = Make(Seq(t1(tf()), PathLambda(AbsClosure(_ => a1))))
            PathApp(App(Projection(compo, 1), u), i)
          })
        }).toMap.updated(si, AbsClosure(i => {
          val u = Make(Seq(u0, PathLambda(AbsClosure(_ => a1))))
          PathApp(App(Projection(compo, 1), u), i)
        }))
      )
    }
    val a1p = Hcomp(A1, a1,
        B1_faces.view.mapValues(bd => {
          // alpha is of type f(t1p) == a1
          AbsClosure(j => PathApp(Projection(pair(bd()), 1), Formula.Neg(j)) )
        }).toMap.updated(si, AbsClosure(_ => a1)))
    Glue(a1p, B1_faces.view.mapValues(bd => () => Projection(pair(bd()), 0)).toMap)
  }

  def hcompGlue(B: GlueType, u0: Value, faces: AbsClosureSystem): Value = {
    def t_tide(trueFace: Value) = {
      hfill(Projection(trueFace, 0), u0, faces)
    }
    def t1(trueFace: Value) = t_tide(trueFace)(Formula.True)
    if (NORMAL_FORM_MODEL) println("unglue created hcomp glue 1")
    val a1 = Hcomp(B.ty, Unglue(B.ty, u0, false, B.faces),
      faces.view.mapValues(_.map(u => {
        if (NORMAL_FORM_MODEL) println("unglue created hcomp glue 2")
        Unglue(B.ty, u, false, B.faces)
      })).toMap ++
      B.faces.view.mapValues(pair0 => AbsClosure(i => {
        val pair = pair0()
        val w = Projection(pair, 1)
        val f = Projection(w, 0)
        App(f, t_tide(pair)(i))
      })).toMap
    )
    Glue(a1, B.faces.view.mapValues(bd => () => t1(bd())).toMap)
  }

  def ghcomp(@stuck_pos tp: Value, base: Value, faces: AbsClosureSystem) = {
    Hcomp(tp, base, faces.updated(Formula.Neg(Formula.Or(faces.keys)), AbsClosure(base)))
  }

  def comp(@stuck_pos tp: AbsClosure, base: Value, faces: AbsClosureSystem) = {
    def default() = {
      Hcomp(
        tp(Formula.True),
        Transp(tp, Formula.False, base),
        faces.view.mapValues(f => AbsClosure(i => forward(tp, i, f(i)))).toMap)
    }
    val dim = Formula.Generic(dgen())
    val appd = tp.apply(dim)
    appd.whnf match {
      case _: PathType =>
        PathLambda(AbsClosure(i => {
          Comp(tp.map(a => a.whnf.asInstanceOf[PathType].typ(i)), PathApp(base, i),
            faces.view.mapValues(_.map(a => PathApp(a, i))).toMap
              .updated(i, AbsClosure(j => tp(j).whnf.asInstanceOf[PathType].right))
              .updated(Formula.Neg(i).simplify, AbsClosure(j => tp(j).whnf.asInstanceOf[PathType].left))
          )
        }))
  //      case r: Record =>
  //        Make(compGraph(r.nodes, i => tp(i).whnf.asInstanceOf[Record].nodes, faces, base, (v, i) => Projection(v, i)))
      case s: Sum if !s.hit && s.noArgs =>
        assert(!s.support().names.contains(dim.id))
        Hcomp(appd, base, faces)
      case a =>
        default()
    }
  }

  def gcomp(@stuck_pos tp: AbsClosure, base: Value, faces: AbsClosureSystem) = {
    ghcomp(
      tp(Formula.True),
      Transp(tp, Formula.False, base),
      faces.view.mapValues(f => AbsClosure(i => forward(tp, i, f(i)))).toMap)
  }




  // create a path from base  => transp, tp is constant on phi
  def transpFill(i: Formula, phi: Formula, tp: AbsClosure, base: Value) =
    Transp(AbsClosure(j => tp(Formula.And(i, j))), Formula.Or(Formula.Neg(i), phi), base)

  // from base => hcomp
  def hfill(tp: Value, base: Value, faces: AbsClosureSystem) = {
    AbsClosure(i =>
      Hcomp(tp, base,
        faces.view.mapValues(f => AbsClosure(j => f(Formula.And(i, j)))).toMap.updated(Formula.Neg(i), AbsClosure(_ => base)))
    )
  }

  def gfill(tp: AbsClosure, base: Value, faces: AbsClosureSystem) = {
    AbsClosure(i =>
      gcomp(AbsClosure(j => tp(Formula.And(i, j))),
        base,
        faces.view.mapValues(f => AbsClosure(j => f(Formula.And(i, j)))).toMap.updated(Formula.Neg(i), AbsClosure(_ => base)))
    )
  }

  // from base => com
  def fill(tp: AbsClosure, base: Value, faces: AbsClosureSystem) = {
    AbsClosure(i =>
      Comp(AbsClosure(j => tp(Formula.And(i, j))),
        base,
        faces.view.mapValues(f => AbsClosure(j => f(Formula.And(i, j)))).toMap.updated(Formula.Neg(i), AbsClosure(_ => base)))
    )
  }

  // here base is of type tp(1), the result is of type tp(0)
  def transp_inv(phi: Formula, tp: AbsClosure, base: Value) =
    Transp(AbsClosure(j => tp(Formula.Neg(j))), phi, base)

  // here base is of type tp(1), the result is transp_inv(...) => base
  def transpFill_inv(i: Formula, phi: Formula, tp: AbsClosure, base: Value) =
    Transp(AbsClosure(j => tp(Formula.And(Formula.Neg(i), Formula.Neg(j)))), Formula.Or(i, phi), base)

  // where i|- A, u: A(i/r), it's type is A(i/1)
  def forward(A: AbsClosure, r: Formula, u: Value) =
    Transp(AbsClosure(i => A(Formula.Or(i, r))), r, u)

  // transp(A, p, a(0)) -> a(1)   : A(1)
  def squeeze(A: AbsClosure, a: AbsClosure, p: Formula) =
    AbsClosure(i => Transp(AbsClosure(j => A(Formula.Or(i, j))), Formula.Or(p, i), a(i)))


  inline def transpFill(graph0: ClosureGraph, graph: Formula => ClosureGraph, phi: Formula, base: Int => Value): Seq[AbsClosure] = {
    val closures = mutable.ArrayBuffer[AbsClosure]()
    for (i <- graph0.graph.indices) {
      val basei = base(i)
      val res = graph0(i) match {
        case _: ClosureGraph.Independent =>
          AbsClosure(j => {
            transpFill(j,
              phi,
              AbsClosure(k => graph(k).graph(i).independent.typ),
              basei
            )
          })
        case _: ClosureGraph.Dependent =>
          val closuresSeq = closures.toSeq
          AbsClosure(j => {
            transpFill(j,
              phi,
              AbsClosure(k => {val tt = graph(k); tt.get(i, j => closuresSeq(j)(k))  }),
              basei
            )
          })
      }
      closures.append(res)
    }
    closures.toSeq
  }


  inline def compGraph(cs0: ClosureGraph, cs: Formula => ClosureGraph, faces: AbsClosureSystem, base: Value, map: (Value, Int) => Value): Seq[Value] = {
    val closures = mutable.ArrayBuffer[AbsClosure]()
    for (i <- cs0.graph.indices) {
      val res = cs0(i) match {
        case _: ClosureGraph.Independent =>
          fill(AbsClosure(j => cs(j)(i).asInstanceOf[ClosureGraph.Independent].typ), map(base, i),
            faces.view.mapValues(_.map(a => map(a, i))).toMap
          )
        case _: ClosureGraph.Dependent =>
          val closuresSeq = closures.toSeq
          fill(
            AbsClosure(k => cs(k).get(i, j => closuresSeq(j)(k))),
            map(base, i),
            faces.view.mapValues(_.map(a => map(a, i))).toMap
          )
      }
      closures.append(res)
    }
    closures.toSeq.map(_.apply(Formula.True))
  }

  inline def hcompGraph(cs: ClosureGraph, faces: AbsClosureSystem, base: Value, map: (Value, Int) => Value): Seq[Value] = {
    val closures = mutable.ArrayBuffer[AbsClosure]()
    for (i <- cs.graph.indices) {
      val res = cs(i) match {
        case in: ClosureGraph.Independent =>
          hfill(in.typ, map(base, i),
            faces.view.mapValues(_.map(a => map(a, i))).toMap
          )
        case com: ClosureGraph.Dependent =>
          val closuresSeq = closures.toSeq
          fill(
            AbsClosure(k => cs.get(i, j => closuresSeq(j)(k))),
            map(base, i),
            faces.view.mapValues(_.map(a => map(a, i))).toMap
          )
      }
      closures.append(res)
    }
    closures.toSeq.map(_.apply(Formula.True))
  }
}
