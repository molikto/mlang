package mlang.compiler.semantic

import mlang.compiler._
import mlang.compiler.semantic.{given, _}
import mlang.compiler.semantic.Assignments
import mlang.utils._
import scala.collection.mutable

object PlatformNominal {

  var hashSet = new mutable.HashSet[AnyRef]()

  def supportShallow(v1: AnyRef): SupportShallow = {
    hashSet.clear()
    supportShallow0(v1)
  }

  private def supportShallow0(v1: AnyRef): SupportShallow = {
    val clz = v1.getClass
    val fs = clz.getDeclaredFields
    var ns = SupportShallow.empty
    for (f <- fs) {
      f.setAccessible(true)
      val o = f.get(v1)
      o match {
        case v: Value =>
          ns = ns ++ v.supportShallow()
        case f: semantic.Formula =>
          ns = ns +- f.names
        case p: Pattern =>
        case a =>
          if (hashSet.contains(a)) {
            val j = 1
          } else {
            hashSet.add(a)
            ns = ns ++ supportShallow0(a)
          }
      }
    }
    ns
  }

  def restrict(v1: AnyRef, v2: Assignments): AnyRef = {
    val clz = v1.getClass
    val fs = clz.getDeclaredFields
    val ns = new Array[AnyRef](fs.size)
    val cons = clz.getDeclaredConstructors
    assert(cons.size == 1)
    var changed = false
    var i = 0
    for (f <- fs) {
      f.setAccessible(true)
      val o = f.get(v1)
      o match {
        case v: Value =>
          val r = v.restrict(v2)
          ns(i) = r
          if (!v.eq(r)) changed = true
        case f: semantic.Formula =>
          val r = f.restrict(v2)
          ns(i) = r
          if (!f.eq(r)) changed = true
        case p: Pattern =>
          ns(i) = p
        case a =>
          // this happens because of the code NOT GENERATED in `Value.scala` has more liberate ways of referring things
          restrict(a, v2)
      }
      i += 1
    }
    if (changed) {
      val c = cons(0)
      c.setAccessible(true)
      c.newInstance(ns : _*).asInstanceOf[AnyRef]
    } else {
      v1
    }
  }

}