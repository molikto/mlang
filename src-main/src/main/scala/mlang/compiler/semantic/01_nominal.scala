package mlang.compiler.semantic

import Value.{Meta, Referential, Generic, GlobalReferential, LocalReferential}
import scala.collection.mutable
import mlang.utils._


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


case class Support(generic: Set[Generic], names: Set[Long], openMetas: Set[Meta])
object Support {
  val empty: Support = Support(Set.empty, Set.empty, Set.empty)
}

private def Nominal_support[T](a: T)(given Nominal[T]): Support = {
    val tested = mutable.Set.empty[Referential]
    val ss = a.supportShallow() // in case of reference, it will just put the reference here
    val toTest = mutable.Set.from(ss.references)
    val names = mutable.Set.from(ss.names)
    while (toTest.nonEmpty) {
      val candidate = toTest.head
      toTest.remove(candidate)
      candidate match {
        case _: GlobalReferential => // skip global reference
        case Generic(id, _typ) if id == 0 => // skip hack generic
        case r: LocalReferential =>
          tested.add(r)
          val cached = r.supportCached()
          if (cached != null) {
            names.addAll(cached.names)
            tested.addAll(cached.openMetas)
          } else {
            if (candidate.referenced != null) {
              val SupportShallow(ns, rs) = candidate.referenced.supportShallow()
              names.addAll(ns)
              toTest.addAll(rs.filterNot(tested))
            } else if (!candidate.isInstanceOf[Value.Generic]) {
              // this is because we use null generic in various cases to look into a closure
              if (candidate.isInstanceOf[Value.Reference]) {
                warn("seems you are defining a recursive value inside a dimension context")
              } else {
                logicError()
              }
            }
          }
      }
    }
    val spt = Support(tested.flatMap {
      case g: Generic => Some(g)
      case _ => None
    }.toSet, names.toSet, tested.flatMap {
      case m@Meta(_: MetaState.Open) => Some(m)
      case _ => None
    }.toSet)
    spt
}

trait Nominal[T] {
  def (t: T) supportShallow(): SupportShallow
  def (t: T) restrict(dav: Assignments): T
  def (t: T) fswap(w: Long, z: Formula): T
  def (t: T) support(): Support = Nominal_support(t)(given this)
}
