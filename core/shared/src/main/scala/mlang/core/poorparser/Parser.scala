package mlang.core.poorparser


import mlang.core.name._

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.{ImplicitConversions, PackratParsers}
import mlang.core.checker.Primitives
import mlang.core.concrete._
import mlang.core.utils._
import mlang.core.concrete.Term._
import mlang.core.name.Name

import scala.util.parsing.combinator.lexical.StdLexical




/**
  *
  * VERY ULGY PARSER for now
  */
trait Parser extends StandardTokenParsers with PackratParsers with ImplicitConversions {






  override val lexical: StdLexical = new StdLexical {
    override def whitespaceChar: Parser[Char] = elem("", _ == '│') | super.whitespaceChar
  }

  lexical.reserved ++= List("ignored","define", "declare", "match", "make", "record", "type", "sum", "inductively", "with_constructors") ++ Primitives.keys
  lexical.delimiters ++= List("{", "}", "[", "]", ":", ",", "(", ")", "─", "┬", "┌", "⊏", "└", "├", "⇒", "→", "+", "-", ";", "=", "@", "\\", ".")

  def delimited[T](a: String, t: Parser[T], b: String): Parser[T] = a ~> t <~ b


  lazy val declaration: PackratParser[Declaration] = define | defineInferred | declare

  lazy val defineModifiers: PackratParser[Seq[Declaration.Modifier]] =
    rep(
      keyword("inductively") ^^ { _ => Declaration.Modifier.Inductively : Declaration.Modifier } |
      keyword("ignored") ^^ { _ => Declaration.Modifier.Ignored } |
      keyword("with_constructor") ^^ { _ => Declaration.Modifier.WithConstructor}
    )

  lazy val define: PackratParser[Declaration.Define] = (keyword("define") ~> defineModifiers ~ ident <~ ":") ~ (term <~ "=") ~ term ^^ { a =>
    Declaration.Define(Name(Text(a._1._1._2)), a._1._1._1, a._1._2, a._2)
  }

  lazy val defineInferred: PackratParser[Declaration.DefineInferred] = (keyword("define") ~> defineModifiers ~ ident <~ "=") ~ term ^^ { a =>
    Declaration.DefineInferred(Name(Text(a._1._2)), a._1._1, a._2)
  }

  lazy val declare: PackratParser[Declaration.Declare] = (keyword("declare") ~> defineModifiers ~ ident <~ ":") ~ term ^^ { a =>
    Declaration.Declare(Name(Text(a._1._2)), a._1._1, a._2)
  }


  lazy val universe: PackratParser[Universe] = keyword("type") ~> delimited("(", numericLit, ")") ^^ {a =>
    Universe(a.toInt)
  } | keyword("type") ^^ { _ => Universe(0) }

  lazy val let: PackratParser[Let] = delimited("{", rep(declaration) ~ term, "}") ^^ { a => Let(a._1, a._2)}

  lazy val teleInner =  rep1sep(opt(rep1(ident) <~ ":") ~ term, ",") ^^ {
    a => a.map(a => NameType(a._1.getOrElse(Seq.empty).map(a => Name(Text(a))), a._2)) }

  lazy val tele: PackratParser[Seq[NameType]] = delimited("(", teleInner, ")")

  //        Primitives.keys.foldLeft[PackratParser[Term]](split) { (p, n) =>
  //          p | (keyword(n) ^^ {_ =>  Primitive(n) })
  //        } |

  lazy val term: PackratParser[Term] =
    ascription |
        let |
        pi |
        lambda |
        patternLambda |
        app|
        record |
        projection |
        sum |
        universe |
        ident ^^ {a => Reference(a)}

  lazy val ascription: PackratParser[Cast] = delimited("(", (term <~ ":") ~ term, ")") ^^ {a => Cast(a._1, a._2)}

  lazy val pi: PackratParser[Function] = (term <~ "⇒") ~ term ^^ { a => Function(Seq(NameType(Seq.empty, a._1)), a._2)} |
    tele ~ ("⇒" ~> term) ^^ {a => Function(a._1, a._2)}

  lazy val atomicPattern: PackratParser[Name.Opt] = "─" ^^ {_ => None: Option[Name]} | ident ^^ { a =>
    Some(Name(Text(a)))
  }

  lazy val lambda: PackratParser[Lambda] = atomicPattern ~ ("→" ~> term) ^^ {a => Lambda(a._1, a._2) }

  lazy val groupPattern: PackratParser[Pattern] =  delimited("(", rep1sep(pattern, ","),")") ^^ { a => Pattern.Group(a) }

  lazy val namedPattern: PackratParser[Pattern] =
    ident ~ delimited("(", rep1sep(pattern, ","),")") ^^ { a => Pattern.NamedGroup(Text(a._1), a._2) }

  lazy val pattern: PackratParser[Pattern] = atomicPattern ^^ { a => Pattern.Atom(a) } | groupPattern | namedPattern

  lazy val patternContinue = ("→" ~> term) | patternLambda

  lazy val patternCaseEmpty: PackratParser[Seq[Case]] = "┬" ^^ { _ => Seq.empty[Case] }

  lazy val patternCaseSingle: PackratParser[Seq[Case]] = "⊏" ~> pattern ~ patternContinue ^^ { a => Seq(Case(a._1, a._2)) }

  lazy val patternMultipleStart: PackratParser[Case] = ("┌" ~> pattern)  ~ patternContinue  ^^ {a => Case(a._1, a._2)}
  lazy val patternMultipleCont: PackratParser[Case] = ("├" ~> pattern)  ~ patternContinue ^^ {a => Case(a._1, a._2)}
  lazy val patternMultipleEnd: PackratParser[Case] = ("└" ~> pattern)  ~ patternContinue ^^ {a => Case(a._1, a._2)}

  lazy val patternMultiple: PackratParser[Seq[Case]] = patternMultipleStart ~ rep(patternMultipleCont) ~ patternMultipleEnd ^^ {a =>
    a._1._1 +: a._1._2 :+ a._2
  }

  lazy val patternCases: PackratParser[PatternLambda] = (patternCaseEmpty | patternCaseSingle | patternMultiple) ^^ {
    a => PatternLambda(a)
  }
  lazy val patternLambda : PackratParser[Term] =  "─" ~> patternContinue ^^ { a => Term.Lambda(None, a) } |  patternCases

  lazy val app: PackratParser[Application] = term ~ delimited("(", repsep(term, ","), ")") ^^ {a => Application(a._1, a._2)}

  lazy val record: PackratParser[Record] = keyword("record") ~> delimited("{", teleInner, "}") ^^ {a => Record(a) }

  lazy val projection: PackratParser[Projection] = (term <~ ".") ~ ident ^^ {a => Projection(a._1, a._2)}

  lazy val sum: PackratParser[Sum] =
    (keyword("sum") ~> delimited("[", repsep(ident ~ opt(tele),","),"]")) ^^ { a =>

      Sum(a.map(b => Term.Constructor(Text(b._1), b._2.getOrElse(Seq.empty[NameType]))))
    }


  def parse(a: String): ParseResult[Module] = (rep(declaration) ^^ { a=> Module(a) })(new PackratReader(new lexical.Scanner(a)))
}