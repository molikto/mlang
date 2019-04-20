package mlang.core

trait Reifier extends Context {

  private class ReifyOnce {

    def reify(v: Value): Abstract = {
      v match {
        case Value.Application(lambda, argument) =>
          ???
        case Value.Projection(make, field) =>
          ???
        case Value.PatternStuck(lambda, stuck) =>
          ???
        case Value.OpenReference(id, typ) =>
          ???
        case Value.RecursiveReference(value) =>
          ???
        case Value.Reference(value) =>
          ???
        case Value.Universe(level) =>
          ???
        case Value.Function(domain, codomain) =>
          ???
        case Value.Record(level, nodes) =>
          ???
        case Value.Make(values) =>
          ???
        case Value.Construct(name, vs) =>
          ???
        case Value.Sum(level, constructors) =>
          ???
        case Value.Lambda(closure) =>
          ???
        case Value.PatternLambda(id, typ, cases) =>
          ???
        case Value.Let(items, body) =>
          ???
        case Value.Maker(s, i) =>
          ???
        case Value.PathType(typ, left, right) =>
          ???
        case Value.PathLambda(body) =>
          ???
        case Value.PathApplication(left, stuck) =>
          ???
      }
    }

    def reify(v: Value.Closure): Abstract = ???
  }

}
