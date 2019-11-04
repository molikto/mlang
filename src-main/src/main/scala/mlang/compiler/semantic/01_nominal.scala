package mlang.compiler.semantic

import Value.{Meta, Referential, Generic}

case class Support(generic: Set[Generic], names: Set[Long], openMetas: Set[Meta])
object Support {
  val empty: Support = Support(Set.empty, Set.empty, Set.empty)
}

case class SupportShallow(names: Set[Long], references: Set[Referential]) {
  def ++(s: SupportShallow) = if (s == SupportShallow.empty) this else SupportShallow(names ++ s.names, references ++ s.references)
  def ++(s: Set[Referential]) = if (s.isEmpty) this else  SupportShallow(names, references ++ s)
  def +-(s: Set[Long]) = if (s.isEmpty) this else SupportShallow(names ++ s, references)
}

object SupportShallow {
  val empty: SupportShallow = SupportShallow(Set.empty, Set.empty)
}

given (sp: Iterable[SupportShallow]) {
  def merge: SupportShallow = SupportShallow(sp.flatMap(_.names).toSet, sp.flatMap(_.references).toSet)
}

given (sp: Option[SupportShallow]) {
  def orEmpty: SupportShallow = sp.getOrElse(SupportShallow.empty)
}


trait Nominal[T] {
  def (t: T) supportShallow(): SupportShallow
  def (t: T) restrict(dav: Assignments): T
  def (t: T) fswap(w: Long, z: Formula): T
}
