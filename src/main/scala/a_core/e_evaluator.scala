package a_core

import java.util.concurrent.atomic.AtomicLong

import com.twitter.util.Eval

import scala.collection.mutable


/**
  * this is a totoally hack, but should be harmless.
  */
object TunnelingHack {

  private val uid = new AtomicLong(0)
  val tunnel = mutable.Map.empty[Long, Value]

  def tunnelingHack(v: Value): String = {
    val a = uid.incrementAndGet()
    tunnel.put(a, v)
    s"TunnelingHack.tunnel(${a}L)"
  }
}

trait Evaluator extends Context[Value] {

  /**
    *
    * we evaluate will **valid typechecked terms** by NBE
    */
  private def emit(term: Term, depth: Int): String = {

    def source(a: String): String = "\"" + a + "\""

    term match {
      case Lambda(domain, body) =>
        val d = depth + 1
        s"LambdaValue(${emit(domain, depth)}, r$d => ${emit(body, d)})"
      case Pi(domain, body) =>
        val d = depth + 1
        s"PiValue(${emit(domain, depth)}, r$d => ${emit(body, d)})"
      case VariableReference(index) =>
        if (index > depth) s"OpenVariableReference(${layerId(index - depth - 1).get}L)"
        else s"r${depth - index}"
      case Application(left, right) =>
        s"${emit(left, depth)}.application(${emit(right, depth)})"
      case Record(fields) =>
        def rec(fs: Seq[Seq[TypeDeclaration]]): String = {
          if (fs.isEmpty) {
            s"AcyclicValuesGraph.empty"
          } else {
            val hd = fs.head
            val d = depth + 1
            s"AcyclicValuesGraph(Map(${hd.map(f => s"${source(f.name)} -> ${emit(f.body, d)}").mkString(", ")}), " +
            s"vs => {${hd.map(f => s"def r${d}_${f.name} = vs(${source(f.name)}))").mkString("; ")}; ${rec(fs.tail)})"
          }
        }
        s"RecordValue(${rec(fields)})"
      case Make(declarations) =>
        val vs = declarations.filter(_.isInstanceOf[ValueDeclaration]).map(_.asInstanceOf[ValueDeclaration])
        val d = depth + 1
        s"{ var hd = new scala.collection.mutable.Map.empty[String, Value](); " +
            s"${vs.map(f => s"def r${d}_${f.name} = hd(${source(f.name)}))").mkString("; ")}; " +
            s"${vs.map(f => s"hd.put(${source(f.name)}, ${emit(f.body, d)})").mkString("; ")}; " +
            s"MakeValue(hd) }"
      case Projection(left, name) =>
        s"${emit(left, depth)}.projection(${source(name)})"
      case DeclarationReference(index, name) =>
        if (index > depth) {
          val ly =  index - depth - 1
          declarationValue(ly, name) match {
            case Some(v) =>
              TunnelingHack.tunnelingHack(v match {
                case MutableProxyValue(Some(a)) =>
                  a
                case _ =>
                  v
              })
            case None =>
              s"OpenDeclarationReference(${layerId(ly).get}L, $name)"
          }
        }
        else s"r${depth - index}_$name)"
      case Sum(ts) =>
        s"SumValue(Map(${ts.map(p => s"${source(p.name)} -> " + emit(p.term, depth)).mkString(", ")}))"
      case Construct(name, data) =>
        s"ConstructValue(${source(name)}, ${emit(data, depth)})"
      case Split(left, right) =>
        val d = depth + 1
        s"${emit(left, depth)}.split(Map(${right.map(p =>s"${source(p.name)} -> (r$d => ${emit(p.term, d)})").mkString(", ")}))"
    }
  }

  // LATER less call to eval, how to make values compositional with contexts?
  protected def eval(term: Term): Value = {
    val source = "import a_core._\n" +  emit(term, -1)

    println("==================")
    println(term)
    println("==================")
    println(source)
    println("==================")
    println("==================")
    val twitterEval = new Eval()
    twitterEval.apply[Value](source)
  }

  private def force(a: Value): Value = {
    a match {
      case MutableProxyValue(to) =>
        to match {
          case Some(v) => v
          case _ => throw new Exception("Forcing empty mutable proxy")
        }
      case _ => a
    }
  }

  protected def equalMvv(m1: Map[String, Value => Value], m2: Map[String, Value => Value]): Boolean = {
    m1.keySet == m2.keySet && m1.forall(pair => {
      val k = pair._1
      val a = pair._2
      val b = m2(k)
      equal(a, b)
    })
  }

  protected def equalMv(m1: Map[String, Value], m2: Map[String, Value]): Boolean = {
    m1.keySet == m2.keySet && m1.forall(pair => {
      val k = pair._1
      val a = pair._2
      val b = m2(k)
      equal(a, b)
    })
  }

  protected def equal(m1: Value => Value, m2: Value => Value): Boolean = {
    val u = OpenVariableReference(newUniqueId())
    equal(m1(u), m2(u))
  }

  def equal(fs: AcyclicValuesGraph, gs: AcyclicValuesGraph): Boolean = {
    equalMv(fs.initials, gs.initials) && {
      val m = fs.initials.mapValues(_ => OpenVariableReference(newUniqueId()))
      m.isEmpty || equal(fs.remaining(m), gs.remaining(m))
    }
  }

  protected def equal(a0: Value, b0: Value): Boolean = {

    val a = force(a0)
    val b = force(b0)
//    if (a.eq(b)) {
//      true
//    } else {
//    }
    (a, b) match {
      case (_: MutableProxyValue, _) => throw new Exception("Not possible")
      case (_, _: MutableProxyValue) => throw new Exception("Not possible")
      case (ProjectionStuck(v1, s1), ProjectionStuck(v2, s2)) => s1 == s2 && equal(v1, v2)
      case (AppStuck(a1, v1), AppStuck(a2, v2)) => equal(a1, a2) && equal(v1, v2)
      case (SplitStuck(s1, m1), SplitStuck(s2, m2)) => equal(s1, s2) && equalMvv(m1, m2)
      case (PiValue(d1, m1), PiValue(d2, m2)) => equal(d1, d2) && equal(m1, m2)
      case (LambdaValue(d1, m1), LambdaValue(d2, m2)) => equal(d1, d2) && equal(m1, m2)
      case (RecordValue(fs), RecordValue(gs)) => equal(fs, gs)
      case (MakeValue(fs), MakeValue(gs)) => equalMv(fs, gs)
      case (SumValue(ts), SumValue(js)) => equalMv(ts, js)
      case (ConstructValue(n1, t1), ConstructValue(n2, t2)) => n1 == n2 && equal(t1, t2)
      case (_, _) => a == b
    }
  }

  protected def nonEmptyJoin(vs: Seq[Value]): Value = {
    assert(vs.tail.forall(a => equal(a, vs.head)), "The join is invalid, we currently only joins equal types")
    vs.head
  }
}

