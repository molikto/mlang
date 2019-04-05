package mlang.utils

import  scala.collection.mutable.{Buffer,Set,Map}
import  scala.collection.immutable


def tarjanCcc[K](g: immutable.Map[K, immutable.Set[K]]): immutable.Set[immutable.Set[K]] = {
  val st = Buffer.empty[K]
  val st_set = Set.empty[K]
  val i = Map.empty[K, Int]
  val lowl = Map.empty[K, Int]
  val rt = Buffer.empty[Buffer[K]]

  def visit(v: K): Unit = {
    i(v) = i.size
    lowl(v) = i(v)
    st += v
    st_set += v

    for (w <- g(v)) {
      if (!i.contains(w)) {
        visit(w)
        lowl(v) = math.min(lowl(w), lowl(v))
      } else if (st_set(w)) {
        lowl(v) = math.min(lowl(v), i(w))
      }
    }

    if (lowl(v) == i(v)) {
      val scc = Buffer.empty[K]
      var w: K | Null = null

      while(v != w) {
        val ww = st.remove(st.size - 1)
        w = ww
        scc += ww
        st_set -= ww
      }

      rt += scc
    }
  }

  for (v <- g.keys) if (!i.contains(v)) visit(v)
  rt.map(_.toSet).toSet
}