package a_core

import java.util.concurrent.atomic.AtomicLong

import com.twitter.util.Eval

import scala.collection.mutable



object TunnelingHack {

  private val uid = new AtomicLong(0)
  private val tunnel = mutable.Map.empty[Long, Value]

  def tunnelingHack(v: Value): String = {
    val a = uid.incrementAndGet()
    tunnel.put(a, v)
    s"TunnelingHack.tunnel($a)"
  }
}

trait Evaluator extends Context[Value] {

  /**
    *
    * we evaluate will **valid typechecked terms** by NBE
    */
  private def emit(term: Term, depth: Int): String = {
    def source(a: String): String = s"\"$a\""
    term match {
      case Lambda(domain, body) =>
        val d = depth + 1
        s"LambdaValue(${emit(domain, depth)}, r$d => ${emit(body, d)})"
      case Pi(domain, body) =>
        val d = depth + 1
        s"PiValue(${emit(domain, depth)}, r$d => ${emit(body, d)})"
      case VariableReference(index) =>
        if (index > depth) s"OpenAbstractionReference(${layerId(index - depth - 1)})"
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
        ???
      case Projection(left, name) =>
        s"${emit(left, depth)}.projection(${source(name)})"
      case DeclarationReference(index, name) =>
        if (index > depth) {
          val ly =  index - depth - 1
          declarationValue(ly, name) match {
            case Some(v) =>
              TunnelingHack.tunnelingHack(v)
            case None =>
              s"OpenDeclarationReference(${layerId(ly)}, $name)"
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
    val source = "import a_core._" +  emit(term, -1)
    val twitterEval = new Eval()
    twitterEval.apply[Value](source)
  }

  protected def equal(a: Value, b: Value): Boolean = {
    if (a.eq(b)) {
      true
    } else {
      ??? // TODO
    }
  }

  protected def nonEmptyJoin(vs: Seq[Value]): Value = {
    assert(vs.tail.forall(a => equal(a, vs.head)), "The join is invalid, we currently only joins equal types")
    vs.head
  }
}

