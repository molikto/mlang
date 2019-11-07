package mlang.compiler.semantic

import mlang.compiler._
import mlang.compiler.semantic.{given, _}
import mlang.compiler.semantic.Assignments
import mlang.utils._
import scala.collection.mutable

object PlatformNominal {


  private def allowedOtherRefs(a: AnyRef): Int = {
    a match {
      case f: scala.Function0[_] =>
        1
      case f: scala.Function1[_, _] =>
        1
      case f: scala.Function2[_, _, _] =>
        1
      case a =>
        if (a.getClass.getName == "mlang.compiler.semantic.10_value_fibrant$package$") 0
        else -1
    }
  }

  def supportShallow(v1: AnyRef): SupportShallow = {
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
        case a =>
          val j = allowedOtherRefs(a)
          if (j > 0) supportShallow(a)
          else if (j == 0) a
          else logicError(a.getClass.getName + " not supported ")
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
        case a =>
          val j = allowedOtherRefs(a)
          if (j > 0) restrict(a, v2)
          else if (j == 0) a
          else logicError(a.getClass.getName + " not supported ")
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