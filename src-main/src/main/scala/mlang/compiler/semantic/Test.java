
package mlang.compiler.semantic;


class Test implements mlang.compiler.Holder {

  @Override public Value value(Object[] vs) {
    return new Value.Lambda(v -> new Value.App( new Value.Universe(0), v));
  }
}