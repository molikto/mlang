package mlang.core

import Abstract._

trait Reifier extends Context {
//
//  private class ReifyOnce {
//
//    def reify(typ: Value, v: Value, d: Int): Abstract = {
//      v match {
//        case Value.OpenReference(id, typ) =>
//          ???
//        case Value.RecursiveReference(value) =>
//          ???
//        case Value.Reference(value) =>
//          ???
//        case Value.Application(lambda, argument) =>
//          Application(reify(lambda, d), reify(argument, d))
//        case Value.Projection(make, field) =>
//          Projection(reify(make, d), field)
//        case Value.PatternStuck(lambda, stuck) =>
//          Application(reify(lambda, d), reify(stuck, d))
//        case Value.Universe(level) =>
//          Universe(level)
//        case Value.Function(domain, codomain) =>
//          Function(reify(domain, d), reify(codomain, d))
//        case Value.Record(level, nodes) =>
//          Record(level, nodes.map(a => RecordNode(a.name, a.dependencies, reify(a.closure, a.dependencies.size, d))))
//        case Value.Maker(s, i) =>
//          Maker(reify(s, d), i)
//        case Value.Make(values) =>
//
//        case Value.Construct(name, vs) =>
//          ???
//        case Value.Sum(level, constructors) =>
//          ???
//        case Value.Lambda(closure) =>
//          ???
//        case Value.PatternLambda(id, typ, cases) =>
//          ???
//        case Value.Let(items, body) =>
//          ???
//        case Value.PathType(typ, left, right) =>
//          ???
//        case Value.PathLambda(body) =>
//          ???
//        case Value.PathApplication(left, stuck) =>
//          ???
//      }
//    }
//
//    def reify(v: Value.MultiClosure, size: Int, d: Int) = ???
//    def reify(domain: Value, v: Value.Closure, d: Int): Abstract = ???
//  }

}
