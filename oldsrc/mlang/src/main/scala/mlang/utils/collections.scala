package mlang.utils


def (s: Seq[T]) firstOption[T, V](a: T => Option[V]): Option[V] = {
  s.find(b => a(b).isDefined).flatMap(a)
}

def (s: Seq[T]) allDistinct[T]: Boolean = s.toSet.size == s.size

def (s: Set[T]) eqUnordered[T](b: Seq[T]) = s.size == b.size && s == b.toSet

def (s: Seq[T]) eqUnordered[T](b: Seq[T]) = s.size == b.size && s.toSet == b.toSet

def (s: Map[Int, T]) toSeqByKey[T]: Seq[T] = s.toSeq.sortBy(_._1).map(_._2)

def (s: Seq[T]) getOrElse[T](i: Int, t: T) = if (i < s.size) s(i) else t

def (map1: Map[A, B]) mergeWith[A, B](map2: Map[A, B], merger: (B, B) => B): Map[A, B] = {
  map1 ++ map2.map{ case (k,v) => k -> map1.get(k).map(a => merger(a, v)).getOrElse(v) }
}