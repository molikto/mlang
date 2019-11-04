package mlang.compiler.semantic


type System[T] = Map[Formula, T]

def [T] (a: System[T]) phi: NormalForm = a.keys.phi

type ValueSystem = System[ValueClosure]
type ClosureSystem = System[Closure]
type MultiClosureSystem = System[MultiClosure]
type AbsClosureSystem = System[AbsClosure]

given [T: Nominal]:  Nominal[System[T]] {
  def (faces: System[T]) supportShallow(): SupportShallow =
    faces.map(f => f._2.supportShallow()  +- f._1.names).merge
  def (faces: System[T]) fswap(w: Long, z: Formula): System[T] =
    faces.map(n => (n._1.fswap(w, z), n._2.fswap(w, z)))
  def (faces: System[T]) restrict(lv: Assignments): System[T] =
    faces.map(n => (n._1.restrict(lv), n._2.restrict(lv)))
}
