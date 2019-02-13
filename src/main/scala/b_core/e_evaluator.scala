package b_core

import java.util.concurrent.atomic.AtomicLong

import a_utils._
import com.twitter.util.Eval

import scala.collection.mutable


/**
  * this is a totally hack, but should be harmless.
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
object PrimitiveValues {

  private val unit = RecordValue(AcyclicValuesGraph.empty)
  private val unit0 = MakeValue(Map.empty)
  private val primitives = Map(
    // value: type
    "type" -> (UniverseValue, UniverseValue),
    "unit" ->  (unit, UniverseValue),
    "unit0" -> (unit0, unit),
    "assert_equal" -> (
        LambdaValue(UniverseValue, (ty, _) => LambdaValue(ty, (a, _) => LambdaValue(ty, (b, _) => {
          assert(CompareValue.equal(a, b))
          unit0
        }))),
        PiValue(UniverseValue, (ty, _) => PiValue(ty, (_, _) => PiValue(ty, (_, _) => unit)))
    ),
    "assert_not_equal" -> (
        LambdaValue(UniverseValue, (ty, _) => LambdaValue(ty, (a, _) => LambdaValue(ty, (b, _) => {
          assert(!CompareValue.equal(a, b))
          unit0
        }))),
        PiValue(UniverseValue, (ty, _) => PiValue(ty, (_, _) => PiValue(ty, (_, _) => unit)))
    )
  )

  val keys = primitives.keySet

  def value(a: String) = primitives(a)._1

  def typ(a: String) = primitives(a)._2
}

trait Evaluator extends Context[Value] {

  def source(a: String): String = "\"" + a + "\""

  private class Emitter(mutuallyDefined: Seq[String] = Seq.empty) {
    /**
      *
      * we evaluate will **valid typechecked terms** by NBE
      */
    def emit(term: Term, depth: Int, isRecursive: Boolean = false): String = {

      term match {
        case Lambda(domain, body) =>
          val d = depth + 1
          val base = s"LambdaValue(${emit(domain, depth)}, (r$d, rd) => ${emit(body, d)})"
          if (isRecursive) s"new $base with RecursiveValue" else base
        case Pi(domain, body) =>
          val d = depth + 1
          s"PiValue(${emit(domain, depth)}, (r$d, rd) => ${emit(body, d)})"
        case VariableReference(index) =>
          if (index > depth) s"OpenVariableReference(${layerId(index - depth - 1).get}L)"
          else s"r${depth - index}"
        case Application(left, right) =>
          s"${emit(left, depth)}.application(${emit(right, depth)}, rd)"
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
          def isRecursive(a: String) = m.mutualDependencies.exists(_.contains(a))
          val d = depth + 1
          s"{ var hd = scala.collection.mutable.Map.empty[String, Value]; " +
              s"${vs.map(f => s"def r${d}_${f.name} = hd(${source(f.name)})); ").mkString("")}" +
              s"${vs.map(f => s"hd.put(${source(f.name)}, ${emit(f.body, d, isRecursive(f.name))}); ").mkString("")}" +
              s"MakeValue(hd.toMap) }"
        case Projection(left, name) =>
          s"${emit(left, depth)}.projection(${source(name)}, rd)"
        case Primitive(name) =>
          s"Primitives.value(${source(name)})"
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
                  s"OpenDeclarationReference(${layerId(ly).get}L, ${source(name)})"
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
          s"${emit(left, depth)}.split(Map(${right.map(p =>s"${source(p.name)} -> ((r$d, rd) => ${emit(p.term, d)})").mkString(", ")}), rd)"
      }
    }
  }

  // LATER less call to eval, how to make values compositional with contexts?
  protected def evalMutualRecursive(vs: Seq[(String, Term)]): Map[String, Value] = {
    val emitter = new Emitter(vs.map(_._1))
    val src = "import b_core._\n" +
        s"{ val rd = FullReduction; var hd = scala.collection.mutable.Map.empty[String, Value]; " +
        vs.map(f => s"def d_${f._1} = hd(${source(f._1)}); ").mkString("") +
        vs.map(f => s"hd.put(${source(f._1)}, ${emitter.emit(f._2, -1, isRecursive = true)}); ").mkString("") +
        s"hd.toMap }"

    debug("==================")
    debug(vs)
    debug("==================")
    debug(src)
    debug("==================")
    val twitterEval = new Eval()
    twitterEval.apply[Map[String, Value]](src)
  }

  protected def eval(term: Term): Value = {
    val src = "import b_core._\n" +
      "{ val rd = FullReduction; " + new Emitter().emit(term, -1) + " }"

    debug("==================")
    debug(term)
    debug("==================")
    debug(src)
    debug("==================")
    val twitterEval = new Eval()
    twitterEval.apply[Value](src)
  }

}

