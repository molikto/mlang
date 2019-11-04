package mlang.compiler.semantic


type ValueClosure = () => Value
given (func: ValueClosure) {
  def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
  def restrict(dav: Assignments): ValueClosure =
    RESTRICT_OBJ.restrict(func, dav).asInstanceOf[ValueClosure]
  def fswap(w: Long, z: Formula): ValueClosure = () => func().fswap(w, z)
}

type Closure = Value => Value
object Closure {
  def apply(a: Value => Value): Closure = a
  def apply(a: Value): Closure = _ => a
}
given (func: Closure) {
  def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
  def restrict(dav: Assignments): Closure =
    RESTRICT_OBJ.restrict(func, dav).asInstanceOf[Value => Value]
  def fswap(w: Long, z: Formula): Closure = d => func(d).fswap(w, z)
}

type AbsClosure = Formula => Value
object AbsClosure {
  def apply(a: Value): AbsClosure = _ => a
  def apply(a: Formula => Value): AbsClosure = a
}
given (func: AbsClosure) {
  def mapd(a: (Value, Formula) => Value): AbsClosure = d => a(func(d), d)
  def map(a: Value => Value): AbsClosure = d => a(func(d))
  def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
  def restrict(dav: Assignments): AbsClosure = 
    RESTRICT_OBJ.restrict(func, dav).asInstanceOf[Formula => Value]
  def fswap(w: Long, z: Formula): AbsClosure = d => func(d).fswap(w, z)
}

type MultiClosure = (Seq[Value], Seq[Formula]) => Value
object MultiClosure {
  def apply(a: Value): MultiClosure = (_, _) => a
  def apply(a: (Seq[Value], Seq[Formula]) => Value): MultiClosure = a
}
given (func: MultiClosure) {
  def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
  def restrict(dav: Assignments): MultiClosure = MultiClosure(RESTRICT_OBJ.restrict(func, dav).asInstanceOf[(Seq[Value], Seq[Formula]) => Value])
  def fswap(w: Long, z: Formula): MultiClosure = MultiClosure((d, k) => func(d, k).fswap(w, z))
}