package mlang.compiler.semantic

import mlang.compiler._
import mlang.utils._
import scala.collection.mutable

object PlatformNominal {


  inline private def allowedOtherRefs(partent: AnyRef, a: AnyRef): Boolean = {
    a match {
      case f: scala.Function0[_] =>
        true
      case f: scala.Function1[_, _] =>
        true
      case f: scala.Function2[_, _, _] =>
        true
      case _: Long =>
        // currently a big hack
        if (partent.getClass.getName.contains("given_Nominal")) {
          false
        } else {
          logicError("Long not supported")
        }
      case a =>
        if (a.getClass.getName.endsWith("$")) false // it seems these are fine
        else {
          val pclz = partent.getClass
          println(pclz.getName)
          // mlang.compiler.MethodRunJava.printByteCode(pclz)
          logicError(a.getClass.getName + " not supported ")
        }
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
        case f: Formula =>
          ns = ns +- f.names
        case g: ClosureGraph =>
          ns = ns ++ g.supportShallow()
        case a: Seq[_] =>
          if (a.nonEmpty) {
            val r = a.head match {
              case Value =>
                a.asInstanceOf[Seq[Value]].map(_.supportShallow()).merge
              case f: Formula =>
                a.asInstanceOf[Seq[Formula]].map(_.supportShallow()).merge
              case _ =>
                logicError()
            }
            ns = ns ++ r
          }
        case a =>
          if (allowedOtherRefs(v1, a)) ns = ns ++ supportShallow(a)
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
        case f: Formula =>
          val r = f.restrict(v2)
          ns(i) = r
          if (!f.eq(r)) changed = true
        case g: ClosureGraph =>
          val r = g.restrict(v2)
          ns(i) = r
          if (!f.eq(r)) changed = true
        case a: Seq[_] =>
          if (a.isEmpty) {
            ns(i) = a
          } else {
            val r = a.head match {
              case Value =>
                a.asInstanceOf[Seq[Value]].map(_.restrict(v2))
              case f: Formula =>
                a.asInstanceOf[Seq[Formula]].map(_.restrict(v2))
              case _ =>
                logicError()
            }
            ns(i) = r
            if (!f.eq(r)) changed = true
          }
        case a =>
          val r = if (allowedOtherRefs(v1, a)) restrict(a, v2) else a
          ns(i) = r
          if (!f.eq(r)) changed = true
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