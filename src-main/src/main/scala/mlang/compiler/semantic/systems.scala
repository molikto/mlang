package mlang.compiler.semantic



type System[T] = Map[Formula, T]

object System {
  def phi[T](a: System[T]) = Formula.phi(a.keys)
}

type ValueSystem = System[Value]
given (faces: ValueSystem) {
  def supportShallow(): SupportShallow =
    SupportShallow.flatten(faces.toSeq.map(f => f._2.supportShallow() +- f._1.names))
  def fswap(w: Long, z: Formula): ValueSystem =
    faces.map(n => (n._1.fswap(w, z), n._2.fswap(w, z)))
  def restrict(lv: Assignments): ValueSystem =
    faces.map(n => (n._1.restrict(lv), n._2.restrict(lv)))
}

type ClosureSystem = System[Closure]
given (faces: ClosureSystem) {
  def supportShallow(): SupportShallow =
    SupportShallow.flatten(faces.toSeq.map(f => f._2.supportShallow() +- f._1.names))
  def fswap(w: Long, z: Formula): ClosureSystem =
    faces.map(n => (n._1.fswap(w, z), n._2.fswap(w, z)))
  def restrict(lv: Assignments): ClosureSystem =
    faces.map(n => (n._1.restrict(lv), n._2.restrict(lv)))
}

type MultiClosureSystem = System[MultiClosure]
object MultiClosureSystem {
  val empty: MultiClosureSystem = Map.empty
}
given (faces: MultiClosureSystem) {
  def supportShallow(): SupportShallow =
    SupportShallow.flatten(faces.toSeq.map(f => f._2.supportShallow() +- f._1.names))
  def fswap(w: Long, z: Formula): MultiClosureSystem =
    faces.map(n => (n._1.fswap(w, z), n._2.fswap(w, z)))
  def restrict(lv: Assignments): MultiClosureSystem =
    faces.map(n => (n._1.restrict(lv), n._2.restrict(lv)))
}

type AbsClosureSystem = System[AbsClosure]
object AbsClosureSystem {
  val empty: AbsClosureSystem = Map.empty
}
given (faces: AbsClosureSystem) {
  def supportShallow(): SupportShallow =
    SupportShallow.flatten(faces.toSeq.map(f => f._2.supportShallow() +- f._1.names))
  def fswap(w: Long, z: Formula): AbsClosureSystem =
    faces.map(n => (n._1.fswap(w, z), n._2.fswap(w, z)))
  def restrict(lv: Assignments): AbsClosureSystem =
    faces.map(n => (n._1.restrict(lv), n._2.restrict(lv)))
}

