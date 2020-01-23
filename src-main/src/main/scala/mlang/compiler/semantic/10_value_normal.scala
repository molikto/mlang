package mlang.compiler.semantic

import mlang.utils._

import Value._

//
// TODO(NORMAL) these are buggy, only reliable on simple construct/makes
// currently the normalizer is only used to check normal forms for debugging usage
// 




def normalFaceV(sys: ValueSystem): ValueSystem = {
  sys
  // sys.toSeq.flatMap(pair => pair._1.normalForm.map(a => (a, pair._2))).map(pair => {
  //   val a = pair._1
  //   val formula = Formula(Set(pair._1))
  //   val bd = pair._2.restrict(pair._1)
  //   (formula, bd.nf)
  // }).toMap
}

def normalFace(sys: AbsClosureSystem): AbsClosureSystem = {
  sys
  // sys.toSeq.flatMap(pair => pair._1.normalForm.map(a => (a, pair._2))).map(pair => {
  //   val a = pair._1
  //   val formula = Formula(Set(pair._1))
  //   val bd = pair._2.restrict(pair._1)
  //   (formula, bd.nf)
  // }).toMap
}

def nf0(v: Value, level: Int = 0): Value = v match {
  case App(left, right) =>
    val res = App(left, nf0(right, level + 1))
    println(s"doing at level $level")
    res.whnf
  case a => a.whnf
}

given Normal[Value] {
  // LATER seems faces.nf will error
  // TODO(NORMAL) we are skipping record and sum


  def (v: Value) nf: Value = v.whnf match {
    case u: Universe => u
    case Function(et, domain, codomain) =>
      Function(et, domain.nf, codomain.nf)
    case Lambda(closure) =>
      Lambda(closure.nf)
    case PatternLambda(id, domain, typ, cases) =>
      PatternLambda(id, domain.nf, typ.nf, cases.map(c => Case(c.pattern, c.closure.nf)))
    case r@Record(inductively, names, nodes) =>
      r
    case Make(values) =>
      Make(values.map(_.nf))
    case SimpleConstruct(name, vs) =>
      SimpleConstruct(name, vs.map(_.nf))
    case HitConstruct(name, vs, ds, ty) =>
      HitConstruct(name, vs.map(_.nf), ds, normalFaceV(ty))
    case s@Sum(_, inductively, _, constructors) =>
      s
    case PathType(typ, left, right) =>
      PathType(typ.nf, left.nf, right.nf)
    case PathLambda(body) =>
      PathLambda(body.nf)
    case App(lambda, argument) =>
      App(lambda.nf, argument.nf)
    case PatternRedux(lambda, stuck) =>
      PatternRedux(lambda, stuck.nf)
    case Projection(make, field) =>
      Projection(make.nf, field)
    case PathApp(left, dimension) =>
      PathApp(left.nf, dimension.simplify)
    case Transp(tp, direction, base) =>
      Transp(tp.nf, direction.simplify, base.nf)
    case Hcomp(tp, base, faces) =>
      Hcomp(tp.nf, base.nf, normalFace(faces))
    case GlueType(tp, faces) => 
      GlueType(tp,  faces)
    case Glue(base, faces) =>
      Glue(base.nf, normalFaceV(faces))
    case Unglue(tp, base, iu, faces) =>
      Unglue(tp.nf, base.nf, iu, normalFaceV(faces))
    case g: Generic => g
    case a => logicError()
  }
}