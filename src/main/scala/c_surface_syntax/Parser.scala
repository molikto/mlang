package c_surface_syntax

import java.util.concurrent.atomic.AtomicLong

import scala.collection.mutable
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.{ImplicitConversions, PackratParsers}
import b_core._


// surface syntax...
object surface {
  sealed abstract class Surface
  sealed abstract class Term
  type Tele = Seq[(Seq[String], Term)]

  case class Definition(name: String, tele: Option[Tele], ty: Option[Term], term: Option[Term]) extends Surface
  case class Definitions(defs: Seq[Definition]) extends Term
  case class Let(defs: Seq[Definition], body: Term) extends Term

  case class Primitive(name: String) extends Term

  case class Ascription(term: Term, right: Term) extends Term
  case class Pi(seq: Tele, body: Term) extends Term
  case class Lambda(seq: Tele, body: Term) extends Term
  case class App(left: Term, right: Seq[Term]) extends Term

  case class Record(seq: Seq[(String, Term)]) extends Term
  case class Make(term: Term, seq: Seq[(String, Term)]) extends Term
  case class Projection(term: Term, str: String) extends Term

  case class Sum(ts: Seq[(String, Option[Term])]) extends Term
  case class Construct(ty: Term, name: String, v: Option[Term]) extends Term
  case class Split(term: Term, right: Seq[(String, Option[String], Term)]) extends Term
  case class Reference(t: String) extends Term

  case object Absent extends Term


  private val gen = new AtomicLong(0)

  // TODO surface syntax should not contain these constructs
  def newValidGeneratedIdent() = s"not_used_${gen.incrementAndGet()}"

  val letId = "not_used_let"
}



/**
  *
  *
  *
  * VERY ULGY PARSER for test purpose only
  *
  *
  */
trait Parser extends StandardTokenParsers with PackratParsers with ImplicitConversions {


  lexical.reserved ++= List("match", "make", "construct", "type")
  lexical.delimiters ++= List("{", "}", "[", "]", ":", ",", "(", ")", "=>", "->", "+", "-", ";", "|", "=", "@", "\\")

  def delimited[T](a: String, t: Parser[T], b: String): Parser[T] = a ~> t <~ b


  lazy val let: PackratParser[surface.Let] = delimited("{", rep(definition) ~ term, "}") ^^ { a => surface.Let(a._1, a._2)}

  lazy val definitions: PackratParser[surface.Definitions] =  keyword("make") ~> delimited( "{", rep(definition) , "}") ^^ { a => surface.Definitions(a)}

  lazy val tele: PackratParser[surface.Tele] = "(" ~> rep1sep((rep1(ident)) ~ opt(":" ~> term), ",") <~ ")" ^^ {a => a.map(a => (a._1, a._2.getOrElse(surface.Absent)))}

  lazy val typedTele: PackratParser[surface.Tele] = "(" ~> rep1sep((rep1(ident) <~ ":") ~ term, ",") <~ ")" ^^ {a => a.map(a => (a._1, a._2))}

  lazy val typedTelePossibleNoName: PackratParser[surface.Tele] = "(" ~> rep1sep(opt((rep1(ident) <~ ":")) ~ term, ",") <~ ")" ^^ {a => a.map(a => (a._1.getOrElse(Seq(surface.newValidGeneratedIdent())), a._2))}

  lazy val definition: PackratParser[surface.Definition] =
    ident ~ opt(typedTele) ~ opt(":" ~> term) ~ opt( "=" ~> term) <~ ";" ^^ {a => surface.Definition(a._1._1._1, a._1._1._2, a._1._2, a._2) }



  lazy val term: PackratParser[surface.Term] =
        ascription |
        definitions |
        keyword("type") ^^ {_ =>  surface.Primitive("type") } |
        let |
        pi |
        lambda |
        app|
        record |
        make |
        projection |
        sum |
        construct |
        split |
        ident ^^ {a => surface.Reference(a)}

  lazy val ascription: PackratParser[surface.Ascription] = delimited("(", (term <~ ":") ~ term, ")") ^^ {a => surface.Ascription(a._1, a._2)}

  lazy val pi: PackratParser[surface.Pi] =
    typedTele ~ ("=>" ~> term) ^^ {a => surface.Pi(a._1, a._2)}

  lazy val lambda: PackratParser[surface.Lambda] =
    tele ~ ("->" ~> term) ^^ {a => surface.Lambda(a._1, a._2) }

  lazy val app: PackratParser[surface.App] = term ~ delimited("(", repsep(term, ","), ")") ^^ {a => surface.App(a._1, a._2)}

  lazy val record: PackratParser[surface.Record] =
    delimited("{", rep(ident ~ (":" ~> term) <~ ";"),"}") ^^ {a => surface.Record(a.map(b => (b._1, b._2)))}

  lazy val make: PackratParser[surface.Make] =
    keyword("make")~> delimited("(", term , ")") ~ delimited("{", rep((ident <~ "=") ~ term <~ ";"), "}") ^^ {a => surface.Make(a._1, a._2.map(a => (a._1, a._2)))}

  lazy val projection: PackratParser[surface.Projection] = (term <~ ".") ~ ident ^^ {a => surface.Projection(a._1, a._2)}

  lazy val sum: PackratParser[surface.Sum] =
    delimited("[", repsep(ident ~ opt(delimited("(", term, ")")),","),"]") ^^ {a => surface.Sum(a.map(k => (k._1, k._2)))}

  lazy val construct: PackratParser[surface.Construct] =
    (term <~ ":") ~ ident ~ opt(delimited("(", term, ")")) ^^ {a => surface.Construct(a._1._1, a._1._2, a._2)}

  lazy val split: PackratParser[surface.Split] =
    (keyword("match") ~> term) ~ delimited("{", rep((ident ~ opt(delimited("(", ident ,")"))) ~ ("->" ~> term <~ ";")), "}") ^^ {a => surface.Split(a._1, a._2.map(k => (k._1._1, k._1._2, k._2)))}

  def parse(a: String): ParseResult[Seq[surface.Definition]] = rep(definition)(new PackratReader(new lexical.Scanner(a)))
}

