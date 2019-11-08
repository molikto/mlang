package mlang.compiler.semantic


type ValueClosure = () => Value

type Closure = Value => Value
object Closure {
  inline def apply(a: Value => Value): Closure = a
  inline def apply(a: Value): Closure = _ => a
}

type AbsClosure = Formula => Value
object AbsClosure {
  inline def apply(a: Value): AbsClosure = _ => a
  inline def apply(a: Formula => Value): AbsClosure = a
}
given (func: AbsClosure) {
  inline def mapd(a: (Value, Formula) => Value): AbsClosure = d => a(func(d), d)
  inline def map(a: Value => Value): AbsClosure = d => a(func(d))
}

type MultiClosure = (Seq[Value], Seq[Formula]) => Value
object MultiClosure {
  inline def apply(a: Value): MultiClosure = (_, _) => a
  inline def apply(a: (Seq[Value], Seq[Formula]) => Value): MultiClosure = a
}


/*

type classes

*/


given Nominal[Closure] {
  def (func: Closure) supportShallow(): SupportShallow = func(Value.Generic.HACK).supportShallow()
  def (func: Closure) restrict(dav: Assignments): Closure = Closure(d => func(Value.Derestricted(d, dav)).restrict(dav))
  def (func: Closure) fswap(w: Long, z: Formula): Closure = d => func(d).fswap(w, z)
}

given Nominal[ValueClosure] {
  def (func: ValueClosure) supportShallow(): SupportShallow = 
    func().supportShallow()
  def (func: ValueClosure) restrict(dav: Assignments): ValueClosure = 
    () => func().restrict(dav)
  def (func: ValueClosure) fswap(w: Long, z: Formula): ValueClosure = () => func().fswap(w, z)
}
given Nominal[AbsClosure] {
  def (func: AbsClosure) supportShallow(): SupportShallow = 
    func(Formula.Generic.HACK).supportShallow()
  def (func: AbsClosure) restrict(dav: Assignments): AbsClosure = 
    AbsClosure(d => func(Formula.Derestricted(d, dav)).restrict(dav))
  def (func: AbsClosure) fswap(w: Long, z: Formula): AbsClosure = d => func(d).fswap(w, z)
}

given Nominal[MultiClosure] {
  def (func: MultiClosure) supportShallow(): SupportShallow =func(Value.Generic.HACKS, Formula.Generic.HACKS).supportShallow()
  def (func: MultiClosure) restrict(dav: Assignments): MultiClosure = MultiClosure((v, d) => func(v.map(a => Value.Derestricted(a, dav)), d.map(a => Formula.Derestricted(a, dav))).restrict(dav))
  def (func: MultiClosure) fswap(w: Long, z: Formula): MultiClosure = MultiClosure((d, k) => func(d, k).fswap(w, z))
}