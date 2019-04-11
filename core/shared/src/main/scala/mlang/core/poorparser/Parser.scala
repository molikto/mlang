//package mlang.core.poorparser
//
//
//import scala.util.parsing.combinator.syntactical.StandardTokenParsers
//import scala.util.parsing.combinator.{ImplicitConversions, PackratParsers}
//import mlang.core.checker.Primitives
//
//
//
//
///**
//  *
//  *
//  *
//  * VERY ULGY PARSER for now
//  *
//  *
//  */
//trait Parser extends StandardTokenParsers with PackratParsers with ImplicitConversions {
//
//
//  lexical.reserved ++= List("match", "make") ++ Primitives.keys
//  lexical.delimiters ++= List("{", "}", "[", "]", ":", ",", "(", ")", "=>", "->", "+", "-", ";", "|", "=", "@", "\\")
//
//  def delimited[T](a: String, t: Parser[T], b: String): Parser[T] = a ~> t <~ b
//
//
//  lazy val let: PackratParser[Let] = delimited("{", rep(definition) ~ term, "}") ^^ { a => Let(a._1, a._2)}
//
//  lazy val definitions: PackratParser[Definitions] =  keyword("make") ~> delimited( "{", rep(definition) , "}") ^^ { a => Definitions(a)}
//
//  lazy val tele: PackratParser[Tele] = "(" ~> rep1sep((rep1(ident)) ~ opt(":" ~> term), ",") <~ ")" ^^ {a => a.map(a => NamedTeleItem(a._1, a._2.getOrElse(Absent)))}
//
//  lazy val typedTele: PackratParser[Tele] = "(" ~> rep1sep((rep1(ident) <~ ":") ~ term, ",") <~ ")" ^^ {a => a.map(a => NamedTeleItem(a._1, a._2))}
//
//  lazy val typedTelePossibleNoName: PackratParser[UnnamedTele] = "(" ~> rep1sep(opt((rep1(ident) <~ ":")) ~ term, ",") <~ ")" ^^ { a =>
//    a.map(a => a._1 match {
//      case Some(l) =>
//        NamedTeleItem(a._1.get, a._2)
//      case None =>
//        UnnamedTeleItem(a._2)
//    })
//  }
//
//  lazy val definition: PackratParser[Definition] =
//    ident ~ opt(typedTele) ~ opt(":" ~> term) ~ opt( "=" ~> term) <~ ";" ^^ {a => Definition(a._1._1._1, a._1._1._2, a._1._2, a._2) }
//
//
//  lazy val term: PackratParser[Term] =
//    ascription |
//        definitions |
//        let |
//        pi |
//        lambda |
//        app|
//        record |
//        projection |
//        inductive |
//        Primitives.keys.foldLeft[PackratParser[Term]](split) { (p, n) =>
//          p | (keyword(n) ^^ {_ =>  Primitive(n) })
//        } |
//        ident ^^ {a => Reference(a)}
//
//  lazy val ascription: PackratParser[Ascription] = delimited("(", (term <~ ":") ~ term, ")") ^^ {a => Ascription(a._1, a._2)}
//
//  lazy val pi: PackratParser[Function] =
//    typedTelePossibleNoName ~ ("=>" ~> term) ^^ {a => Function(a._1, a._2)}
//
//  lazy val lambda: PackratParser[Lambda] =
//    tele ~ ("->" ~> term) ^^ {a => Lambda(a._1, a._2) }
//
//  lazy val app: PackratParser[Application] = term ~ delimited("(", repsep(term, ","), ")") ^^ {a => Application(a._1, a._2)}
//
//  lazy val record: PackratParser[Record] =
//    delimited("{", rep(ident ~ (":" ~> term) <~ ";"),"}") ^^ {a => Record(a.map(b => (b._1, b._2)))}
//
//  lazy val projection: PackratParser[Projection] = (term <~ ".") ~ ident ^^ {a => Projection(a._1, a._2)}
//
//  lazy val inductive: PackratParser[Inductive] =
//    delimited("[", repsep(ident ~ opt(tele),","),"]") ^^ {a => Inductive(a.map(k => (k._1, k._2.getOrElse(Seq.empty))))}
//
//  lazy val split: PackratParser[Split] =
//    (keyword("match") ~> term) ~ delimited("{", rep((ident ~ opt(delimited("(", repsep(ident, ",") ,")"))) ~ ("->" ~> term <~ ";")), "}") ^^ {a => Split(a._1, a._2.map(k => (k._1._1, k._1._2, k._2)))}
//
//  def parse(a: String): ParseResult[Seq[Definition]] = rep(definition)(new PackratReader(new lexical.Scanner(a)))
//}