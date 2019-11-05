package mlang.compiler.semantic

import mlang.compiler.GenLong.Negative.{dgen, gen}
import mlang.utils._
import mlang.compiler.Pattern
import mlang.compiler.semantic.Formula
import scala.annotation.Annotation
import scala.collection.mutable
import Value._



given Nominal[Value.Inductively] {
    def (i: Inductively) restrict(lv: Assignments): Inductively = Inductively(i.id, i.typ.restrict(lv), i.ps.map(_.restrict(lv)))
    def (i: Inductively) fswap(w: Long, z: Formula): Inductively = Inductively(i.id, i.typ.fswap(w, z), i.ps.map(_.fswap(w, z)))
    def (i: Inductively) supportShallow(): SupportShallow = i.typ.supportShallow() ++ i.ps.map(_.supportShallow()).merge
}

given Nominal[Value] {

  def (t: Value) supportShallow(): SupportShallow = t match {
    case Universe(level) => SupportShallow.empty
    case Function(domain, impict, codomain) => domain.supportShallow() ++ codomain.supportShallow()
    case Lambda(closure) => closure.supportShallow()
    case PatternLambda(id, domain, typ, cases) =>
      domain.supportShallow() ++ typ.supportShallow() ++ cases.map(_.closure.supportShallow()).merge
    case Record(inductively, names, nodes) =>
      inductively.map(_.supportShallow()).orEmpty ++ nodes.supportShallow()
    case Make(values) => values.map(_.supportShallow()).merge
    case SimpleConstruct(name, vs) =>
      vs.map(_.supportShallow()).merge
    case HitConstruct(name, vs, ds, ty) =>
      (vs.map(_.supportShallow()) ++ ds.map(_.supportShallow())).merge ++ ty.supportShallow()
    case Sum(inductively, _, constructors) =>
      inductively.map(_.supportShallow()).orEmpty ++ constructors.map(a => a.nodes.supportShallow()).merge
    case PathType(typ, left, right) =>
      typ.supportShallow() ++ left.supportShallow() ++ right.supportShallow()
    case PathLambda(body) => body.supportShallow()
    case App(lambda, argument) => lambda.supportShallow() ++ argument.supportShallow()
    case PatternRedux(lambda, stuck) => lambda.supportShallow() ++ stuck.supportShallow()
    case Projection(make, field) => make.supportShallow()
    case PathApp(left, dimension) => left.supportShallow() +- dimension.names
    case Transp(tp, direction, base) => tp.supportShallow() ++ base.supportShallow() +- direction.names
    case Comp(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ faces.supportShallow()
    case Hcomp(tp, base, faces) => tp.supportShallow() ++ base.supportShallow() ++ faces.supportShallow()
    case GlueType(tp, faces) => tp.supportShallow()++ faces.supportShallow()
    case Glue(base, faces) => base.supportShallow() ++ faces.supportShallow()
    case Unglue(tp, base, iu, faces) => tp.supportShallow() ++ base.supportShallow() ++ faces.supportShallow()
    case referential: Referential => SupportShallow.empty ++ Set(referential)
  }

  /**
    * fresh swap, the id being swapped cannot be used after. this helps because no need for Deswap...
    */
  def (t: Value) fswap(w: Long, z: Formula): Value = t match {
    case u: Universe => u
    case Function(domain, im, codomain) => Function(domain.fswap(w, z), im, codomain.fswap(w, z))
    case Record(inductively, ns, nodes) =>
      Record(inductively.map(_.fswap(w, z)), ns, nodes.fswap(w, z))
    case Make(values) => Make(values.map(_.fswap(w, z)))
    case SimpleConstruct(name, vs) => SimpleConstruct(name, vs.map(_.fswap(w, z)))
    case HitConstruct(name, vs, ds, ty) => HitConstruct(name, vs.map(_.fswap(w, z)), ds.map(_.fswap(w, z)), ty.fswap(w, z))
    case Sum(inductively, hit, constructors) =>
      Sum(inductively.map(_.fswap(w, z)), hit, constructors.map(_.fswap(w, z)))
    case Lambda(closure) => Lambda(closure.fswap(w, z))
    case PatternLambda(id, dom, typ, cases) =>
      PatternLambda(id, dom.fswap(w, z), typ.fswap(w, z), cases.map(a => Case(a.pattern, a.closure.fswap(w, z))))
    case PathType(typ, left, right) =>
      PathType(typ.fswap(w, z), left.fswap(w, z), right.fswap(w, z))
    case PathLambda(body) => PathLambda(body.fswap(w, z))
    case App(lambda, argument) => App(lambda.fswap(w, z), argument.fswap(w, z))
    case t@Transp(tp, direction, base) => Transp(tp.fswap(w, z), direction.fswap(w, z), base.fswap(w, z))
    case h@Hcomp(tp, base, faces) => Hcomp(tp.fswap(w, z), base.fswap(w, z), faces.fswap(w, z))
    case Comp(tp, base, faces) => Comp(tp.fswap(w, z), base.fswap(w, z), faces.fswap(w, z))
    case p@Projection(make, field) => Projection(make.fswap(w, z), field)
    case PatternRedux(lambda, stuck) =>
      PatternRedux(lambda.fswap(w, z).asInstanceOf[PatternLambda], stuck.fswap(w, z))
    case PathApp(left, stuck) => PathApp(left.fswap(w, z), stuck.fswap(w, z))
    case GlueType(base, faces) => GlueType(base.fswap(w, z), faces.fswap(w, z))
    case Glue(base, faces) => Glue(base.fswap(w, z), faces.fswap(w, z))
    case Unglue(tp, base, iu, faces) => Unglue(tp.fswap(w, z), base.fswap(w, z), iu, faces.fswap(w, z))
    case g: Referential => g.getFswap(w, z)
  }

  def (t: Value) restrict(lv: Assignments): Value = if (lv.isEmpty) t else t match {
    case u: Universe => u
    case Function(domain, im, codomain) =>
      Function(domain.restrict(lv), im, codomain.restrict(lv))
    case Record(inductively, ns, nodes) =>
      Record(inductively.map(_.restrict(lv)), ns, nodes.restrict(lv))
    case Make(values) =>
      Make(values.map(_.restrict(lv)))
    case SimpleConstruct(name, vs) =>
      SimpleConstruct(name, vs.map(_.restrict(lv)))
    case HitConstruct(name, vs, ds, ty) =>
      HitConstruct(name, vs.map(_.restrict(lv)), ds.map(_.restrict(lv)), ty.restrict(lv))
    case Sum(inductively, hit, constructors) =>
      Sum(inductively.map(_.restrict(lv)), hit, constructors.map(_.restrict(lv)))
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
    case t@Transp(tp, direction, base) =>
      Transp(tp.restrict(lv), direction.restrict(lv), base.restrict(lv))
    case h@Hcomp(tp, base, faces) =>
      Hcomp(tp.restrict(lv), base.restrict(lv), faces.restrict(lv))
    case Comp(tp, base, faces) =>
      Comp(tp.restrict(lv), base.restrict(lv), faces.restrict(lv))
    case p@Projection(make, field) =>
      Projection(make.restrict(lv), field)
    case PatternRedux(lambda, stuck) =>
      PatternRedux(lambda.restrict(lv).asInstanceOf[PatternLambda], stuck.restrict(lv))
    case PathApp(left, stuck) =>
      PathApp(left.restrict(lv), stuck.restrict(lv))
    case GlueType(base, faces) =>
      GlueType(base.restrict(lv), faces.restrict(lv))
    case Glue(base, faces) =>
      Glue(base.restrict(lv), faces.restrict(lv))
    case Unglue(tp, base, iu, faces) =>
      Unglue(tp.restrict(lv), base.restrict(lv), iu, faces.restrict(lv))
    case g: Referential =>
      g.getRestrict(lv)
  }
}