package mlang.compiler.semantic

import Value._
import mlang.compiler.GenLong.Negative.{dgen, gen}
import scala.collection.mutable


def hcompHcompUniverse(u: Universe, b: Value, es: AbsClosureSystem, base: Value, faces: AbsClosureSystem): Value = {
  val wts = es.map((pair: (Formula, AbsClosure)) => {
    val al = pair._1
    val eal = pair._2
    val ret = AbsClosure(i =>
      transp_inv(Formula.False, eal, hfill(eal( Formula.True), base, faces).apply(i))
    )
    (al, ret)
  })
  val t1s = es.map((pair: (Formula, AbsClosure)) => {
    val al = pair._1
    val eal = pair._2
    val ret = Hcomp(eal(Formula.True), u, faces)
    (al, ret)
  })
  val esmap = es.view.mapValues(a => PathLambda(a)).toMap
  val v = Unglue(b, u, true, esmap)
  val vs = faces.map((pair: (Formula, AbsClosure)) => {
    val al = pair._1
    val ual = pair._2
    val ret = ual.map(v =>
      Unglue(b, v, true, esmap)
    )
    (al, ret)
  })
  val v1 = Hcomp(b, v, vs ++ wts)
  Glue(v1, t1s)
}

def transpHcompUniverse(A: Value, es: AbsClosureSystem, dim: Formula.Generic, si: Formula, u0: Value): Value = {
  // this mapping is done in hcomp in cubicaltt
  val A0 = A.fswap(dim.id, Formula.False)
  val A1 = A.fswap(dim.id, Formula.True)
  val es0 = es.fswap(dim.id, Formula.False)
  val es1 = es.fswap(dim.id, Formula.True)

  // this is UnglueU in cubicaltt, the es0 is a system of path lambdas
  val v0 = Unglue(A0, u0, true, es0.view.mapValues(a => PathLambda(a)).toMap)

  val faces_elim_dim = es.toSeq.map(a => (a._1.elim(dim.id), a._2)).filter(_._1.normalForm != NormalForm.False).toMap
  val t1s = faces_elim_dim.view.mapValues(p => {
    Transp(AbsClosure(i => p(Formula.True).fswap(dim.id, i)), si, u0)
  }).toMap
  val v1 = comp(AbsClosure(i => A.fswap(dim.id, i)), v0,
    faces_elim_dim.map((pair: (Formula, AbsClosure)) => {
      val abs = AbsClosure(i => {
        transp_inv(Formula.False, pair._2.fswap(dim.id, i),
          transpFill(i, si, AbsClosure(i => pair._2(Formula.True).fswap(dim.id, i)), u0)
        )
      })
      (pair._1, abs)
    }).updated(si, AbsClosure(_ => v0)))
  val sys = t1s.updated(si, u0)
  val fibersys_ = es1.map((pair: (Formula, AbsClosure)) => {
    val eq = pair._2
    val b = v1
    val as = sys
    val dg = Formula.Generic(dgen())
    val res = eq(dg).whnf match {
      case s: Sum if s.noArgs =>
        // because we know this is non-dependent
        val p1 = Hcomp(eq(dg), b, as.view.mapValues(a => AbsClosure(_ => a)).toMap)
        val p2 = hfill(eq(dg), b, as.view.mapValues(a => AbsClosure(_ => a)).toMap)
        (p1: Value, p2: AbsClosure)
      case other =>
        val adwns = as.map((pair: (Formula, Value)) => {
          (pair._1, AbsClosure(j => transpFill_inv(j, Formula.False, eq, pair._2)))
        }).toMap
        val left = fill(eq, b, adwns)
        val a = comp(eq, b, adwns)
        val right = AbsClosure(j =>
          transpFill_inv(j, Formula.False, eq, a)
        )
        val p = AbsClosure(i =>
          comp(AbsClosure(a => eq(Formula.Neg(a))), a,
            adwns.updated(Formula.Neg(i), left).updated(i, right).view.mapValues(v => AbsClosure(j => v(Formula.Neg(j)))).toMap
          )
        )
        (a : Value, p: AbsClosure)
    }
    (pair._1, res)
  }).toMap
  val t1s_ = fibersys_.view.mapValues(_._1).toMap
  val v1_ = Hcomp(A1, v1, fibersys_.view.mapValues(_._2).toMap.updated(si, AbsClosure(_ => v1)))
  Glue(v1_, t1s_)
}

def transpGlue(B: GlueType, dim: Formula.Generic, si: Formula, u0: Value): Value = {
  def B_swap(f: Formula) = B.fswap(dim.id, f).asInstanceOf[GlueType]
  val B0 = B_swap(Formula.False)
  def A_swap(i: Formula) = B.ty.fswap(dim.id, i)
  val B1 = B_swap(Formula.True)
  val A1 = B1.ty
  val A0 = B0.ty
  // a0: A(i/0)
  val a0 = Unglue(A0, u0, false, B0.faces)
  // defined in phi_elim_i
  def t_tide(trueFace: Value, i: Formula) = {
    transpFill(i, si, AbsClosure(i => {
    Projection(trueFace.fswap(dim.id, i), 0)
    }), u0)
  }
  val faces_elim_dim = B.faces.toSeq.map(a => (a._1.elim(dim.id), a._2)).filter(_._1.normalForm != NormalForm.False).toMap
  val B1_faces = B1.faces.filter(_._1.normalForm != NormalForm.False)
  def t1(trueFace: Value) = t_tide(trueFace, Formula.True)
  // a1: A(i/1) and is defined on both si and elim(i, phi)
  val a1 = gcomp(
    AbsClosure(i => A_swap(i)),
    a0,
    faces_elim_dim.view.mapValues(tf => {
      AbsClosure(i => {
        val EQi  = tf.fswap(dim.id, i)
        val w = Projection(EQi, 1)
        App(Projection(w, 0), t_tide(tf, i))
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
          val u = Make(Seq(t1(tf), PathLambda(AbsClosure(_ => a1))))
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
        AbsClosure(j => PathApp(Projection(pair(bd), 1), Formula.Neg(j)) )
      }).toMap.updated(si, AbsClosure(_ => a1)))
    Glue(a1p, B1_faces.view.mapValues(bd => Projection(pair(bd), 0)).toMap)
}

def hcompGlue(B: GlueType, u0: Value, faces: AbsClosureSystem): Value = {
  def t_tide(trueFace: Value) = {
    hfill(Projection(trueFace, 0), u0, faces)
  }
  def t1(trueFace: Value) = t_tide(trueFace)(Formula.True)
  val a1 = Hcomp(B.ty, Unglue(B.ty, u0, false, B.faces),
    faces.view.mapValues(_.map(u => Unglue(B.ty, u, false, B.faces))).toMap ++
    B.faces.view.mapValues(pair => AbsClosure(i => {
      val w = Projection(pair, 1)
      val f = Projection(w, 0)
      App(f, t_tide(pair)(i))
    })).toMap
  )
  Glue(a1, B.faces.view.mapValues(bd => t1(bd)).toMap)
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
    case PathType(typ, left, right) =>
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
      assert(!appd.support().names.contains(dim.id))
      Hcomp(appd, base, faces)
    case _ =>
      default()
  }
}

def gcomp(@stuck_pos tp: AbsClosure, base: Value, faces: AbsClosureSystem) = {
  ghcomp(
    tp(Formula.True),
    Transp(tp, Formula.False, base),
    faces.view.mapValues(f => AbsClosure(i => forward(tp, i, f(i)))).toMap)
}



def compGraph(cs0: ClosureGraph, cs: Formula => ClosureGraph, faces: AbsClosureSystem, base: Value, map: (Value, Int) => Value): Seq[Value] = {
  val closures = mutable.ArrayBuffer[AbsClosure]()
  for (i <- cs0.graph.indices) {
    val res = cs0(i) match {
      case _: ClosureGraph.Independent =>
        fill(AbsClosure(j => cs(j)(i).asInstanceOf[ClosureGraph.Independent].typ), map(base, i),
          faces.view.mapValues(_.map(a => map(a, i))).toMap
        )
      case _: ClosureGraph.Dependent =>
        fill(
          AbsClosure(k => cs(k).get(i, j => closures(j)(k))),
          map(base, i),
          faces.view.mapValues(_.map(a => map(a, i))).toMap
        )
    }
    closures.append(res)
  }
  closures.toSeq.map(_.apply(Formula.True))
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


def transpFill(graph0: ClosureGraph, graph: Formula => ClosureGraph, phi: Formula, base: Int => Value): Seq[AbsClosure] = {
  val closures = mutable.ArrayBuffer[AbsClosure]()
  for (i <- graph0.graph.indices) {
    val res = graph0(i) match {
      case _: ClosureGraph.Independent =>
        AbsClosure(j => {
          transpFill(j,
            phi,
            AbsClosure(k => graph(k).graph(i).independent.typ),
            base(i)
          )
        })
      case _: ClosureGraph.Dependent =>
        AbsClosure(j => {
          transpFill(j,
            phi,
            AbsClosure(k => {val tt = graph(k); tt.get(i, j => closures(j)(k))  }),
            base(i)
          )
        })
    }
    closures.append(res)
  }
  closures.toSeq
}


def hcompGraph(cs: ClosureGraph, faces: AbsClosureSystem, base: Value, map: (Value, Int) => Value): Seq[Value] = {
  val closures = mutable.ArrayBuffer[AbsClosure]()
  for (i <- cs.graph.indices) {
    val res = cs(i) match {
      case in: ClosureGraph.Independent =>
        hfill(in.typ, map(base, i),
          faces.view.mapValues(_.map(a => map(a, i))).toMap
        )
      case com: ClosureGraph.Dependent =>
        fill(
          AbsClosure(k => cs.get(i, j => closures(j)(k))),
          map(base, i),
          faces.view.mapValues(_.map(a => map(a, i))).toMap
        )
    }
    closures.append(res)
  }
  closures.toSeq.map(_.apply(Formula.True))
}
