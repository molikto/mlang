package mlang.compiler.semantic


object Closures {
  opaque type Closure = Value => Value
  object Closure {
    def apply(a: Value => Value): Closure = a
    def apply(a: Value): Closure = _ => a
  }
  given (func: Closure) {
    def apply(seq: Value): Value = func(seq)
    def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
    def restrict(dav: Assignments): Closure =
      RESTRICT_OBJ.restrict(func, dav).asInstanceOf[Value => Value]
    def fswap(w: Long, z: Formula): Closure = d => func(d).fswap(w, z)
  }

  opaque type AbsClosure = Formula => Value
  object AbsClosure {
    def apply(a: Value): AbsClosure = _ => a
    def apply(a: Formula => Value): AbsClosure = a
  }
  given (func: AbsClosure) {
    def apply(seq: Formula): Value = func(seq)
    def mapd(a: (Value, Formula) => Value): AbsClosure = d => a(func(d), d)
    def map(a: Value => Value): AbsClosure = d => a(func(d))
    def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
    def restrict(dav: Assignments): AbsClosure = 
      RESTRICT_OBJ.restrict(func, dav).asInstanceOf[Formula => Value]
    def fswap(w: Long, z: Formula): AbsClosure = d => func(d).fswap(w, z)
  }

  opaque type MultiClosure = (Seq[Value], Seq[Formula]) => Value
  object MultiClosure {
    def apply(a: Value): MultiClosure = (_, _) => a
    def apply(a: (Seq[Value], Seq[Formula]) => Value): MultiClosure = a
  }
  given (func: MultiClosure) {
    def apply(seq: Seq[Value], ds: Seq[Formula]): Value = func(seq, ds)
    def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
    def restrict(dav: Assignments): MultiClosure = MultiClosure(RESTRICT_OBJ.restrict(func, dav).asInstanceOf[(Seq[Value], Seq[Formula]) => Value])
    def fswap(w: Long, z: Formula): MultiClosure = MultiClosure((d, k) => func(d, k).fswap(w, z))
  }
}

export Closures.Closure
export Closures.AbsClosure
export Closures.MultiClosure