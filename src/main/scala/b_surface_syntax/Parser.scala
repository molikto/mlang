package b_surface_syntax

import scala.collection.mutable
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.{ImplicitConversions, PackratParsers}
import a_core._

trait Parser extends StandardTokenParsers with PackratParsers with ImplicitConversions {


  // surface syntax...
  object surface {
    sealed abstract class Surface
    sealed abstract class Term

    case class Module(defs: Seq[Definition]) extends Surface
    // def name = value
    case class Definition(name: String, term: Term) extends Surface

    // fix a =>
    case class Fix(name: String, t: Term) extends Term
    // (a : b)
    case class Ascription(term: Term, right: Term) extends Term
    // (a: term, c: term) => (b: term) => term => term
    case class Pi(seq: Seq[(Option[String], Term)], body: Term) extends Term
    // lam (x: term, y: term) => lam (x, y) => ...
    case class Lambda(seq: Seq[(String, Option[Term])], body: Term) extends Term
    // a(b, b, c)
    case class App(left: Term, right: Seq[Term]) extends Term

    // [a: term, b: term]
    case class Record(seq: Seq[(String, Term)]) extends Term
    // [a = term, b = term]
    case class Record(seq: Seq[(String, Term)]) extends Term
    // a.b
    case class Projection(term: Term, str: String) extends Term

    // fix a => [zero, succ@ a]
    case class Sum(ts: Seq[(String, Term)]) extends Term
    // zero[]
    case class Construct(name: String, v: Term) extends Term
    // split
    //   #zero => ....
    //   #succ one two =>
    case class Split(term: Term, right: Seq[(String, String, Term)]) extends Term
    case class Reference(t: String) extends Term
  }

  lexical.reserved ++= List("def", "fix", "cast", "as", "split")
  lexical.delimiters ++= List("{", "}", "[", "]", ":", ",", "(", ")", "=>", "->", "+", "-", ";", "|", "=", "@", "\\")

  def delimited[T](a: String, t: Parser[T], b: String) = a ~> t <~ b


  lazy val module: PackratParser[surface.Module] =
    rep(definition) ^^ { a => surface.Module(a)}

  lazy val definition: PackratParser[surface.Definition] =
    (keyword("def") ~> ident <~ "=") ~ (term) ^^ {a => surface.Definition(a._1, a._2)}

  lazy val term: PackratParser[surface.Term] =
    ascription |
        fix |
        pi |
        lambda |
        app|
        record |
        Record |
        projection |
        sum |
        construct |
        split |
        ident ^^ {a => surface.Reference(a)}

  lazy val fix: PackratParser[surface.Fix] = (keyword("fix") ~> ident <~ "->") ~ term ^^ {a => surface.Fix(a._1, a._2)}

  lazy val ascription: PackratParser[surface.Ascription] = (keyword("cast") ~> term <~ keyword("as")) ~ term ^^ {a => surface.Ascription(a._1, a._2)}

  lazy val pi: PackratParser[surface.Pi] =
    delimited("(",
      repsep( ((ident <~ ":") ~ term) ^^ {a => (Some(a._1), a._2)} | term ^^ {a => (None, a)}, ","),
      ")") ~ ("=>" ~> term) ^^ {a => surface.Pi(a._1, a._2)}

  lazy val lambda: PackratParser[surface.Lambda] =
    delimited("(",
      repsep(((ident <~ ":") ~ term) ^^ { a => (a._1, Some(a._2)) } | ident ^^ { a => (a, None) }, ","),
      ")") ~ ("->" ~> term) ^^ {a => surface.Lambda(a._1, a._2) }

  lazy val app: PackratParser[surface.App] = term ~ delimited("(", repsep(term, ","), ")") ^^ {a => surface.App(a._1, a._2)}

  lazy val Record: PackratParser[surface.Record] =
    delimited("{", rep1sep(ident ~ (":" ~> term), ","),"}") ^^ {a => surface.Record(a.map(b => (b._1, b._2)))}

  lazy val record: PackratParser[surface.Record] =
    delimited("{", repsep(ident ~ ("=" ~> term), ","),"}") ^^ {a => surface.Record(a.map(b => (b._1, b._2)))}

  lazy val projection: PackratParser[surface.Projection] = (term <~ ".") ~ ident ^^ {a => surface.Projection(a._1, a._2)}

  lazy val sum: PackratParser[surface.Sum] =
    delimited("[", rep1sep((ident <~ "@") ~ term,","),"]") ^^ {a => surface.Sum(a.map(k => (k._1, k._2)))}

  lazy val construct: PackratParser[surface.Construct] =
    (ident <~ "#") ~ term ^^ {a => surface.Construct(a._1, a._2)}

  lazy val split: PackratParser[surface.Split] =
    ("split" ~> term) ~ rep1((ident <~ "#") ~ (ident <~ "->") ~ term) ^^ {a => surface.Split(a._1, a._2.map(k => (k._1._1, k._1._2, k._2)))}

  def parse(a: String): ParseResult[surface.Module] = module(new PackratReader(new lexical.Scanner(a)))

  def transform(a: surface.Module): Module = {
    val defs = mutable.Set.empty[String]
    def term(a: surface.Term, context: Seq[(String, Int) => Option[Term]]): Term = {

      def RecordTerms(seq: Seq[(String, surface.Term)]): Seq[Term] = {
        seq.foldLeft((context, Seq.empty[Term])) { (c, t) =>
          (((n: String, i: Int) => if (t._1 == n) Some(VariableReference(i)) else None) +: c._1, c._2 :+ term(t._2, c._1))
        }._2
      }

      def piToRecordType(seq: Seq[(String, surface.Term)]): Term = Record(seq.indices.map("_" + _), RecordTerms(seq))

      def piToRecordContext(seq: Seq[String]) = {
        ((n: String, i: Int) => {
          val index = seq.indexOf(n)
          if (index >= 0) {
            Some(Projection(VariableReference(i), "_" + index))
          } else None
        }) +: context
      }

      a match {
        case surface.Fix(name, t) =>
          Fix(term(t, ((n: String, i: Int) => if (n == name) Some(VariableReference(i)) else None) +: context))
        case surface.Ascription(a, b) =>
          Ascription(term(a, context), term(b, context))
        case surface.Pi(seq, body) =>
          val ss = seq.map(a => (a._1.getOrElse(""), a._2))
          Pi(piToRecordType(ss), term(body, piToRecordContext(ss.map(_._1))))
        case surface.Lambda(seq, body) =>
          if (seq.forall(_._2.nonEmpty)) {
            val ts = seq.map(a => (a._1, a._2.get))
            Lambda(Some(piToRecordType(ts)), term(body, piToRecordContext(ts.map(_._1))))
          } else if (seq.forall(_._2.isEmpty)) {
            Lambda(None, term(body, piToRecordContext(seq.map(a => a._1))))
          } else throw new Exception("")
        case surface.App(left, rs) =>
          App(term(left, context), Record(rs.indices.map("_" + _), rs.map(a => term(a, context))))
        case surface.Record(seq) =>
          Record(seq.map(_._1), RecordTerms(seq))
        case surface.Record(seq) =>
          Record(seq.map(_._1), seq.map(a => term(a._2, context)))
        case surface.Projection(t, seq) =>
          Projection(term(t, context), seq)
        case surface.Sum(ts) =>
          Sum(ts.map(a => a._1 -> term(a._2, context)).toMap)
        case surface.Construct(name, v) =>
          Construct(name, term(v, context))
        case surface.Split(t, ts) =>
          Split(term(t, context), ts.map(a => a._1 -> {term(a._3, ((n: String, i: Int) => if(n == a._2) Some(VariableReference(i)) else None) +: context)}).toMap)
        case surface.Reference(n) =>
          var c = context
          var i = 0
          while (c.nonEmpty) {
            c.head(n, i) match {
              case Some(t) => return t
              case _ => Unit
            }
            i += 1
            c = c.tail
          }
          if (defs(n)) GlobalReference(n)
          else throw new Exception("Name not resolved " + n)
      }
    }
    Module(a.defs.map(d => {
      val res = (d.name, term(d.term, Seq.empty))
      defs += d.name
      res
    }))
  }
}

import DebugLevel._
object ParseTests extends scala.App with TypeCheck {

  val parser = new Parser {}
  val txt = io.Source.fromFile("library/prelude.edt").getLines().mkString("\n")

  val parsed = parser.parse(txt)

  if (parsed.next.atEnd) {
    delog("Parsed " + parsed.get)
    val transformed = parser.transform(parsed.get)
    check(transformed)
  } else {
    val endPos = parsed.next.pos
    throw new Exception("Parse failed " + endPos.line + ", " + endPos.column)
  }
}
