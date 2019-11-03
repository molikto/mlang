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
  def flatten(ss: Seq[SupportShallow]): SupportShallow = SupportShallow(ss.flatMap(_.names).toSet, ss.flatMap(_.references).toSet)
  def orEmpty(a: Option[SupportShallow]): SupportShallow = a.getOrElse(empty)
}