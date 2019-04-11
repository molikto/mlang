package mlang.core.utils
import  scala.collection.mutable.{Buffer,Set,Map}
import  scala.collection.immutable


object graphs {


  def tarjanCcc[T](g: immutable.Map[T, immutable.Set[T]]): immutable.Set[immutable.Set[T]] = {
    val st = Buffer.empty[T]
    val st_set = Set.empty[T]
    val i = Map.empty[T, Int]
    val lowl = Map.empty[T, Int]
    val rt = Buffer.empty[Buffer[T]]

    def visit(v: T): Unit = {
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
        val scc = Buffer.empty[T]
        var w: Option[T] = None

        while(v != w.orNull) {
          w = Some(st.remove(st.size - 1))
          scc += w.get
          st_set -= w.get
        }

        rt += scc
      }
    }

    for (v <- g.keys) if (!i.contains(v)) visit(v)
    rt.map(_.toSet).toSet
  }
}
