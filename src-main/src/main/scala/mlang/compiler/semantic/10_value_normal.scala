package mlang.compiler.semantic

import mlang.utils._

import Value._

given Normal[Value] {
  // LATER seems faces.nf will error
  // FIXME we are skipping record and sum
  def (v: Value) nf: Value = v.whnf match {
    case u: Universe => u
    case Function(domain, impict, codomain) =>
      Function(domain.nf, impict, codomain.nf)
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
      HitConstruct(name, vs.map(_.nf), ds, ty.map(n => (n._1, n._2.nf)))
    case s@Sum(inductively, _, constructors) =>
      s
    case PathType(typ, left, right) =>
      PathType(typ.nf, left.nf, right.nf)
    case PathLambda(body) =>
      PathLambda(body.nf)
    case App(lambda, argument) =>
      App(lambda.nf, argument.nf)
    case PatternRedux(lambda, stuck) =>
      PatternRedux(lambda.nf.asInstanceOf[PatternLambda], stuck.nf)
    case Projection(make, field) =>
      Projection(make.nf, field)
    case PathApp(left, dimension) =>
      PathApp(left.nf, dimension)
    case Transp(tp, direction, base) =>
      Transp(tp.nf, direction, base.nf)
    case Hcomp(tp, base, faces) =>
      Hcomp(tp.nf, base.nf,  faces.map(n => (n._1, n._2.nf)))
    case GlueType(tp, faces) => 
      GlueType(tp.nf,  faces.map(n => (n._1, n._2.nf)))
    case Glue(base, faces) =>
      Glue(base.nf,  faces.map(n => (n._1, n._2.nf)))
    case Unglue(tp, base, iu, faces) =>
      Unglue(tp.nf, base.nf, iu,  faces.map(n => (n._1, n._2.nf)))
    case g: Generic => g
    case _ => logicError()
  }
}