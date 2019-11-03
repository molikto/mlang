package mlang.compiler.semantic



type System[T] = Map[Formula, T]
object System {
  def phi[T](a: System[T]) = Formula.phi(a.keys)
}


implicit class Closure(private val func: Value => Value) extends AnyVal {
  def eq(b: Closure): Boolean = func.eq(b.func)
  def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
  def restrict(dav: Assignments): Closure = Closure(RESTRICT_OBJ.restrict(func, dav).asInstanceOf[Value => Value])
  def fswap(w: Long, z: Formula): Closure = Closure(d => func(d).fswap(w, z))

  def apply(seq: Value): Value = func(seq)
}

object Closure {
  def apply(a: Value): Closure = Closure(_ => a)
}



object AbsClosure {
  def apply(a: Value): AbsClosure = AbsClosure(_ => a)
}

// LATER make sure AnyVal classes is eliminated in bytecode
implicit class AbsClosure(private val func: Formula => Value) extends AnyVal {
  def eq(b: AbsClosure): Boolean = func.eq(b.func)
  def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
  def mapd(a: (Value, Formula) => Value): AbsClosure = AbsClosure(d => a(this(d), d))
  def map(a: Value => Value): AbsClosure = AbsClosure(d => a(this(d)))
  def restrict(dav: Assignments): AbsClosure = AbsClosure(RESTRICT_OBJ.restrict(func, dav).asInstanceOf[Formula => Value])
  def fswap(w: Long, z: Formula): AbsClosure = AbsClosure(d => func(d).fswap(w, z))

  def apply(seq: Formula): Value = func(seq)
}

implicit class MultiClosure(private val func: (Seq[Value], Seq[Formula]) => Value) extends AnyVal {
  def eq(b: MultiClosure): Boolean = func.eq(b.func)
  def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
  // def apply() = func(Seq.empty, Seq.empty)
  def restrict(dav: Assignments): MultiClosure = MultiClosure(RESTRICT_OBJ.restrict(func, dav).asInstanceOf[(Seq[Value], Seq[Formula]) => Value])
  def fswap(w: Long, z: Formula): MultiClosure = MultiClosure((d, k) => func(d, k).fswap(w, z))

  def apply(seq: Seq[Value], ds: Seq[Formula]): Value = func(seq, ds)

}

object AbsMultiClosureSystem {
  val empty = AbsMultiClosureSystem(_ => Map.empty)
}
implicit class AbsMultiClosureSystem(private val func: Seq[Formula] => MultiClosureSystem) extends AnyVal {
  def eq(b: AbsMultiClosureSystem): Boolean = func.eq(b.func)
  def supportShallow(): SupportShallow = RESTRICT_OBJ.supportShallow(func)
  // def apply() = func(Seq.empty, Seq.empty)
  def restrict(dav: Assignments): AbsMultiClosureSystem = AbsMultiClosureSystem(RESTRICT_OBJ.restrict(func, dav).asInstanceOf[Seq[Formula] => MultiClosureSystem])
  def fswap(w: Long, z: Formula): AbsMultiClosureSystem =
    AbsMultiClosureSystem(d => MultiClosureSystem.fswap(func(d), w, z))

  def apply(ds: Seq[Formula]): MultiClosureSystem= func(ds)
}



type ValueSystem = System[Value]
object ValueSystem {
  def supportShallow(faces: ValueSystem): SupportShallow = {
    SupportShallow.flatten(faces.toSeq.map(f => f._2.supportShallow() +- f._1.names))
  }
  def fswap(faces: ValueSystem, w: Long, z: Formula): ValueSystem = {
    faces.toSeq.map(n => (n._1.fswap(w, z), n._2.fswap(w, z))).toMap
  }
  def restrict(faces: ValueSystem, lv: Assignments) = {
    // you cannot remove faces here! it has bugs with derestricted!!
    faces.toSeq.map(n => (n._1.restrict(lv), n._2.restrict(lv))).toMap
  }
}

type ClosureSystem = System[Closure]
object ClosureSystem {
  def supportShallow(faces: ClosureSystem): SupportShallow = {
    SupportShallow.flatten(faces.toSeq.map(f => f._2.supportShallow() +- f._1.names))
  }
  def fswap(faces: ClosureSystem, w: Long, z: Formula): ClosureSystem = {
    faces.toSeq.map(n => (n._1.fswap(w, z), n._2.fswap(w, z))).toMap
  }
  def restrict(faces: ClosureSystem, lv: Assignments) = {
    // you cannot remove faces here! it has bugs with derestricted!!
    faces.toSeq.map(n => (n._1.restrict(lv), n._2.restrict(lv))).toMap
  }
}

type MultiClosureSystem = System[MultiClosure]
object MultiClosureSystem {
  val empty: MultiClosureSystem = Map.empty

  def supportShallow(faces: MultiClosureSystem): SupportShallow = {
    SupportShallow.flatten(faces.toSeq.map(f => f._2.supportShallow() +- f._1.names))
  }
  def fswap(faces: MultiClosureSystem, w: Long, z: Formula): MultiClosureSystem = {
    faces.toSeq.map(n => (n._1.fswap(w, z), n._2.fswap(w, z))).toMap
  }
  def restrict(faces: MultiClosureSystem, lv: Assignments) = {
    // you cannot remove faces here! it has bugs with derestricted!!
    faces.toSeq.map(n => (n._1.restrict(lv), n._2.restrict(lv))).toMap
  }
}

type AbsClosureSystem = System[AbsClosure]
object AbsClosureSystem {
  val empty: AbsClosureSystem = Map.empty
  def supportShallow(faces: AbsClosureSystem): SupportShallow = {
    SupportShallow.flatten(faces.toSeq.map(f => f._2.supportShallow() +- f._1.names))
  }
  def fswap(faces: AbsClosureSystem, w: Long, z: Formula): AbsClosureSystem = {
    faces.toSeq.map(n => (n._1.fswap(w, z), n._2.fswap(w, z))).toMap
  }
  def restrict(faces: AbsClosureSystem, lv: Assignments) = {
    // you cannot remove faces here! it has bugs with derestricted!!
    faces.toSeq.map(n => (n._1.restrict(lv), n._2.restrict(lv))).toMap
  }
}

