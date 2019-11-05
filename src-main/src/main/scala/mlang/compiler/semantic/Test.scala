package mlang.compiler.semantic

class TestScala extends mlang.compiler.Holder {

  override def value(vs: Array[Any]) = {
    Value.Lambda.apply(v => Value.App.apply(Value.Universe.apply(0), Value.PathLambda.apply(d => 
      Value.Lambda.apply(c => Value.PathApp(v, d))
      )))
  }
}