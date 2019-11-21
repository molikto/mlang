package mlang.compiler.semantic

import scala.collection.immutable.ArraySeq


class TestScala extends mlang.compiler.Holder {

  override def value(vs: Array[Object]) = {
    // Value.Lambda.apply(v => 
    //   Value.Lambda.apply(_ => v))

      // Value.PathApp(Value.Universe(0), 
      // Formula.Or.apply(Formula.Neg.apply(Formula.True),
      // Formula.And.apply(Formula.True, Formula.False)))

    // Value.Lambda.apply(v => Value.App.apply(Value.Universe.apply(0), Value.PathLambda.apply(d => 
    //   Value.Lambda.apply(c => Value.PathApp(v, d))
    //   )))

    // Value.PatternLambda(123131232131L, Value.Universe(0), null, Seq(Case(null, MultiClosure((a, b) => {
    //   // captuers..
    //   // args expanded
    //   val a1 = a(0)
    //   val a2 = a(2)
    //   val c = mlang.compiler.ByteCodeGeneratorRun.getPattern(0)
    //   // metas
    //   a1
    // }))))

    // Value.Glue(null, Map((Formula.True, () => Value.Universe(0)), (Formula.False, () => Value.Universe(2))))

    // val a = Seq(Value.Universe(0), Value.Universe(1))
    // val b = a(1)
    // Value.Make(Seq(Value.Record(None, mlang.compiler.ByteCodeGeneratorRun.getNames(0), null), Value.Record(Option(Inductively(1, null, null)), null, null)))

    // val a: scala.Function0[Value] = () => Value.Universe(0)
    // a()

    val a = Value.Record(null, null, ClosureGraph.apply(
      Seq(
        ClosureGraphArguments(false, ArraySeq.empty, 1, (a, b) => (Seq(Value.LocalMeta(null), Value.LocalMeta(null)), Value.Universe(7))),
        ClosureGraphArguments(false, new ArraySeq.ofInt(Array[Int](0, 1,2)), 1, (a, b) => (Seq(Value.LocalMeta(null), Value.LocalMeta(null)), Value.Universe(7)))
      ),
      5,
      fs => Seq(
        (Formula.True, (vs: Seq[Value], ms: Seq[Value]) => vs(0))
      ).toMap
    ))
    a
  }
}