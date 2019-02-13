package a_utils
import  scala.collection.mutable.{Buffer,Set,Map}
import  scala.collection.immutable


object GraphAlgorithms {




  def tarjanCcc(g: immutable.Map[String, immutable.Set[String]]): immutable.Set[immutable.Set[String]] = {
    val st = Buffer.empty[String]
    val st_set = Set.empty[String]
    val i = Map.empty[String, Int]
    val lowl = Map.empty[String, Int]
    val rt = Buffer.empty[Buffer[String]]

    def visit(v: String): Unit = {
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
        val scc = Buffer.empty[String]
        var w: String = null

        while(v != w) {
          w = st.remove(st.size - 1)
          scc += w
          st_set -= w
        }

        rt += scc
      }
    }

    for (v <- g.keys) if (!i.contains(v)) visit(v)
    rt.map(_.toSet).toSet
  }
}
