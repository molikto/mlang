package mlang.compiler.semantic

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

    Value.Glue(null, Map((Formula.True, () => Value.Universe(0)), (Formula.False, () => Value.Universe(2))))
  }
}