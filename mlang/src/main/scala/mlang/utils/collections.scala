package mlang.utils


def (s: Seq[T]) firstOption[T, V](a: T => Option[V]): Option[V] = {
  s.find(b => a(b).isDefined).flatMap(a)
}

def (s: Seq[T]) allDistinct[T]: Boolean = s.toSet.size == s.size

def (s: Set[T]) eqUnordered[T](b: Seq[T]) = s.size == b.size && s == b.toSet

def (s: Seq[T]) eqUnordered[T](b: Seq[T]) = s.size == b.size && s.toSet == b.toSet