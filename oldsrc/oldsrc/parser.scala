package mlang.surface_syntax

import scala.language.implicitConversions
import java.util.concurrent.atomic.AtomicLong

import scala.collection.mutable
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.{ImplicitConversions, PackratParsers}
import mlang.core

/**
  *
  *
  *
  * VERY ULGY PARSER for now
  *
  *
  */
trait Parser extends StandardTokenParsers with PackratParsers with ImplicitConversions {


  lexical.reserved ++= List("match", "make") ++ core.primitives.keys
  lexical.delimiters ++= List("{", "}", "[", "]", ":", ",", "(", ")", "=>", "->", "+", "-", ";", "|", "=", "@", "\\")

  def delimited[T](a: String, t: Parser[T], b: String): Parser[T] = a ~> t <~ b


  lazy val let: PackratParser[Term] = delimited("{", rep(definition) ~ term, "}") ^^ { a => Term.Let(a._1, a._2)}

  lazy val definitions: PackratParser[Term] =  keyword("make") ~> delimited( "{", rep(definition) , "}") ^^ { a => Term.Definitions(a)}

  lazy val tele: PackratParser[Tele] = "(" ~> rep1sep((rep1(ident)) ~ opt(":" ~> term), ",") <~ ")" ^^ {a => a.map(a => TeleItem.Named(a._1, a._2.getOrElse(Term.Absent)))}

  lazy val typedTele: PackratParser[Tele] = "(" ~> rep1sep((rep1(ident) <~ ":") ~ term, ",") <~ ")" ^^ {a => a.map(a => TeleItem.Named(a._1, a._2))}

  lazy val typedTelePossibleNoName: PackratParser[UnnamedTele] = "(" ~> rep1sep(opt((rep1(ident) <~ ":")) ~ term, ",") <~ ")" ^^ { a =>
    a.map(a => a._1 match {
      case Some(l) =>
        TeleItem.Named(a._1.get, a._2)
      case None =>
        TeleItem.Unnamed(a._2)
    })
  }

  lazy val definition: PackratParser[Definition] =
    ident ~ opt(typedTele) ~ opt(":" ~> term) ~ opt( "=" ~> term) <~ ";" ^^ {a => Definition(a._1._1._1, a._1._1._2, a._1._2, a._2) }


  lazy val term: PackratParser[Term] =
        ascription |
        definitions |
        let |
        pi |
        lambda |
        app|
        record |
        make |
        projection |
        inductive |
        construct |
        core.primitives.keys.foldLeft[PackratParser[Term]](split) { (p, n) =>
          p | (keyword(n) ^^ {_ =>  Term.Primitive(n) })
        } |
        ident ^^ {a => Term.Reference(a)}

  lazy val ascription: PackratParser[Term] = delimited("(", (term <~ ":") ~ term, ")") ^^ {a => Term.Ascription(a._1, a._2)}

  lazy val pi: PackratParser[Term] =
    typedTelePossibleNoName ~ ("=>" ~> term) ^^ {a => Term.Pi(a._1, a._2)}

  lazy val lambda: PackratParser[Term] =
    tele ~ ("->" ~> term) ^^ {a => Term.Lambda(a._1, a._2) }

  lazy val app: PackratParser[Term] = term ~ delimited("(", repsep(term, ","), ")") ^^ {a => Term.App(a._1, a._2)}

  lazy val record: PackratParser[Term] =
    delimited("{", rep(ident ~ (":" ~> term) <~ ";"),"}") ^^ {a => Term.Record(a.map(b => (b._1, b._2)))}

  lazy val make: PackratParser[Term] =
    keyword("make")~> delimited("(", term , ")") ~ delimited("{", rep((ident <~ "=") ~ term <~ ";"), "}") ^^ {a => Term.Make(a._1, a._2.map(a => (a._1, a._2)))}

  lazy val projection: PackratParser[Term] = (term <~ ".") ~ ident ^^ {a => Term.Projection(a._1, a._2)}

  lazy val inductive: PackratParser[Term] =
    delimited("[", repsep(ident ~ opt(tele),","),"]") ^^ {a => Term.Inductive(a.map(k => (k._1, k._2.getOrElse(Seq.empty))))}

  lazy val construct: PackratParser[Term] =
    (term <~ ":") ~ ident ~ opt(delimited("(", repsep(term, ","), ")")) ^^ {a => Term.Construct(a._1._1, a._1._2, a._2)}

  lazy val split: PackratParser[Term] =
    (keyword("match") ~> term) ~ delimited("{", rep((ident ~ opt(delimited("(", repsep(ident, ",") ,")"))) ~ ("->" ~> term <~ ";")), "}") ^^ {a => Term.Split(a._1, a._2.map(k => (k._1._1, k._1._2, k._2)))}

  def parse(a: String): ParseResult[Seq[Definition]] = rep(definition)(new PackratReader(new lexical.Scanner(a)))
}

