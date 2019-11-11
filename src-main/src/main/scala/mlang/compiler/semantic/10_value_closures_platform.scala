package mlang.compiler.semantic

import mlang.compiler._
import mlang.utils._
import scala.collection.mutable

// 7bb567a is the commit that uses lazy restrict, it seems to be safer?
object PlatformNominal {


  inline private def allowedOtherRefs(parent: AnyRef, a: AnyRef): Boolean = {
    a match {
      case f: scala.Function0[_] =>
        true
      case f: scala.Function1[_, _] =>
        true
      case f: scala.Function2[_, _, _] =>
        true
      case _: Long =>
        // currently a big hack
        val pn = parent.getClass.getName
        if (pn.contains("given_Nominal") || pn.contains("ClosureGraph")) {
          false
        } else {
          logicError("Long not supported")
        }
      case _: Int =>
        if (parent.getClass.getName.contains("value_fibrant")) { // these are indexes
          false
        } else {
          logicError("Int not supported")
        }
      case a =>
        if (a.getClass.getName.endsWith("$")) false // it seems these are fine
        else {
          val pclz = parent.getClass
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
          // ns = ns ++ g.supportShallow()
        case a: Map[_, _] =>
          if (a.nonEmpty) {
            val seq = a.toSeq
            ns = ns ++ (seq.head._1 match {
              case _: Formula =>
                seq.head._2 match {
                  case _: scala.Function0[_] =>
                    a.asInstanceOf[System[ValueClosure]].supportShallow()
                  case _: scala.Function1[_, _] =>
                    a.asInstanceOf[System[AbsClosure]].supportShallow()
                  case _ =>
                    logicError()
                }
              case _ => logicError()
            })
          }
        case a: Seq[_] =>
          if (a.nonEmpty) {
            val r = a.head match {
              case Value =>
                a.asInstanceOf[Seq[Value]].map(_.supportShallow()).merge
              case f: Formula =>
                a.asInstanceOf[Seq[Formula]].map(_.supportShallow()).merge
              case _: scala.Function1[_, _] =>
                a.asInstanceOf[Seq[scala.Function1[_, _]]].map(a => supportShallow(a)).merge
              case _ =>
                SupportShallow.empty
                // logicError()
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
    if (cons.size != 1) 
      logicError() 
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
        case a: Map[_, _] =>
          if (a.isEmpty) {
            ns(i) = a
          } else {
            val seq = a.toSeq
            val r = seq.head._1 match {
              case _: Formula =>
                seq.head._2 match {
                  case _: scala.Function0[_] =>
                    a.asInstanceOf[System[ValueClosure]].restrict(v2)
                  case _: scala.Function1[_, _] =>
                    a.asInstanceOf[System[AbsClosure]].restrict(v2)
                  case _ =>
                    a
                }
              case _ => logicError()
            }
            ns(i) = r
          }
        case a: Seq[_] =>
          if (a.isEmpty) {
            ns(i) = a
          } else {
            val r = a.head match {
              case Value =>
                a.asInstanceOf[Seq[Value]].map(_.restrict(v2))
              case f: Formula =>
                a.asInstanceOf[Seq[Formula]].map(_.restrict(v2))
              case _: scala.Function1[_, _] =>
                a.asInstanceOf[Seq[scala.Function1[_, _]]].map(a => restrict(a, v2))
              case _ =>
                a
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