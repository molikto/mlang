package b_core

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
object Primitives {

  private val unit = RecordValue(AcyclicValuesGraph.empty)
  val primitives = Map(
    // value: type
    "type" -> (UniverseValue, UniverseValue),
    "unit" ->  (unit, UniverseValue),
    "unit0" -> (MakeValue(Map.empty), unit)
  )
}

trait Evaluator extends Context[Value] {

  def source(a: String): String = "\"" + a + "\""

  private class Emitter(mutuallyDefined: Seq[String] = Seq.empty) {
    /**
      *
      * we evaluate will **valid typechecked terms** by NBE
      */
    def emit(term: Term, depth: Int): String = {

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
        case Cast(a, _) =>
          emit(a, depth) // ignore casts in values
        case r@Record(fs) =>
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
          s"RecordValue(${rec(r.nonDependentLayers.map(_.map(n => fs.find(_.name == n).get)))})"
        case m@Make(_) =>
          val vs = m.valueDeclarations
          val d = depth + 1
          s"{ var hd = scala.collection.mutable.Map.empty[String, Value]; " +
              s"${vs.map(f => s"def r${d}_${f.name} = hd(${source(f.name)})); ").mkString("")}" +
              s"${vs.map(f => s"hd.put(${source(f.name)}, ${emit(f.body, d)}); ").mkString("")}" +
              s"MakeValue(hd.toMap) }"
        case Projection(left, name) =>
          s"${emit(left, depth)}.projection(${source(name)})"
        case Primitive(name) =>
          s"Primitives.primitives(${source(name)})._1"
        case DeclarationReference(index, name) =>
          if (index > depth) {
            val ly =  index - depth - 1
            declarationValue(ly, name) match {
              case Some(v) =>
                TunnelingHack.tunnelingHack(v)
              case None =>
                if (ly == 0 && mutuallyDefined.contains(name)) {
                  s"d_$name"
                } else {
                  s"OpenDeclarationReference(${layerId(ly).get}L, $name)"
                }
            }
          } else {
            s"r${depth - index}_$name"
          }
        case Sum(ts) =>
          s"SumValue(Set(${ts.map(a => source(a.name)).mkString(", ")}), " +
              s"name => name match { ${ts.map(p => s"case ${source(p.name)} => " + emit(p.term, depth)).mkString("; ")}})"
        case Construct(name, data) =>
          s"ConstructValue(${source(name)}, ${emit(data, depth)})"
        case Split(left, right) =>
          val d = depth + 1
          s"${emit(left, depth)}.split(Map(${right.map(p =>s"${source(p.name)} -> (r$d => ${emit(p.term, d)})").mkString(", ")}))"
      }
    }
  }

  // LATER less call to eval, how to make values compositional with contexts?
  protected def eval(vs: Seq[(String, Term)]): Map[String, Value] = {
    val emitter = new Emitter(vs.map(_._1))
    val src = "import b_core._\n" +
        s"{ var hd = scala.collection.mutable.Map.empty[String, Value]; " +
        vs.map(f => s"def d_${f._1} = hd(${source(f._1)}); ").mkString("") +
        vs.map(f => s"hd.put(${source(f._1)}, ${emitter.emit(f._2, -1)}); ").mkString("") +
        s"hd.toMap }"

    println("==================")
    println(vs)
    println("==================")
    println(src)
    println("==================")
    val twitterEval = new Eval()
    twitterEval.apply[Map[String, Value]](src)
  }

  // LATER less call to eval, how to make values compositional with contexts?
  protected def eval(term: Term): Value = {
    val src = "import b_core._\n" +  new Emitter().emit(term, -1)

    println("==================")
    println(term)
    println("==================")
    println(src)
    println("==================")
    val twitterEval = new Eval()
    twitterEval.apply[Value](src)
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

  protected def equal(a: Value, b: Value): Boolean = {
    if (a.eq(b)) {
      true
    } else {
      (a, b) match {
        case (ProjectionStuck(v1, s1), ProjectionStuck(v2, s2)) => s1 == s2 && equal(v1, v2)
        case (AppStuck(a1, v1), AppStuck(a2, v2)) => equal(a1, a2) && equal(v1, v2)
        case (SplitStuck(s1, m1), SplitStuck(s2, m2)) => equal(s1, s2) && equalMvv(m1, m2)
        case (PiValue(d1, m1), PiValue(d2, m2)) => equal(d1, d2) && equal(m1, m2)
        case (LambdaValue(d1, m1), LambdaValue(d2, m2)) => equal(d1, d2) && equal(m1, m2)
        case (RecordValue(fs), RecordValue(gs)) => equal(fs, gs)
        case (MakeValue(fs), MakeValue(gs)) => equalMv(fs, gs)
        case (SumValue(ks, ts), SumValue(gs, js)) => ks == gs && ks.forall(k => ts(k) == js(k))
        case (ConstructValue(n1, t1), ConstructValue(n2, t2)) => n1 == n2 && equal(t1, t2)
        case (_, _) => a == b
      }
    }
  }

  protected def nonEmptyJoin(vs: Seq[Value]): Value = {
    assert(vs.tail.forall(a => equal(a, vs.head)), "The join is invalid, we currently only joins equal types")
    vs.head
  }
}

