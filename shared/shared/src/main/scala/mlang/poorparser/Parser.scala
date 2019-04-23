package mlang.poorparser


import mlang.name._

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.{ImplicitConversions, PackratParsers}
import mlang.concrete._
import mlang.utils._
import mlang.concrete.Term._
import mlang.name.Name

import scala.util.parsing.combinator.lexical.StdLexical




/**
  *
  * VERY ULGY PARSER for now
  */
trait Parser extends StandardTokenParsers with PackratParsers with ImplicitConversions {






  override val lexical: StdLexical = new StdLexical {
    override def whitespaceChar: Parser[Char] = elem("", _ == '│') | super.whitespaceChar
  }

  lexical.reserved ++= List("define", "declare", "case", "__debug", "as", "coe", "hcom", "com","field", "ignored", "match", "make", "record", "type", "sum", "inductively", "with_constructors")
  lexical.delimiters ++= List("{", "}", "[", "]", ":", ",", "(", ")", "≡", "─", "┬", "┌", "⊏", "└", "├", "⇒", "→", "+", "-", ";", "=", "@", "\\", ".", "|")

  def delimited[T](a: String, t: Parser[T], b: String): Parser[T] = a ~> t <~ b


  lazy val declaration: PackratParser[Declaration] =declare |  define

  lazy val defineModifiers: PackratParser[Seq[Declaration.Modifier]] =
    rep(
      keyword("inductively") ^^ { _ => Declaration.Modifier.Inductively : Declaration.Modifier } |
      keyword("ignored") ^^ { _ => Declaration.Modifier.Ignored } |
      keyword("with_constructor") ^^ { _ => Declaration.Modifier.WithConstructor} |
      keyword("__debug") ^^ { _ => Declaration.Modifier.__Debug }
    )

  lazy val define: PackratParser[Declaration.Define] = (keyword("define") ~> defineModifiers ~ ident) ~ opt(tele) ~ opt(":" ~> term) ~ ("=" ~> term) ^^ { a =>
    Declaration.Define(a._1._1._1._1, Name(Text(a._1._1._1._2)), a._1._1._2.getOrElse(Seq.empty), a._1._2, a._2)
  }

  lazy val declare: PackratParser[Declaration.Declare] = (keyword("declare") ~> defineModifiers ~ ident) ~ opt(tele) ~ (":" ~> term) ^^ { a =>
    Declaration.Declare( a._1._1._1, Name(Text(a._1._1._2)), a._1._2.getOrElse(Seq.empty), a._2)
  }


  lazy val universe: PackratParser[Universe] = keyword("type") ~> delimited("(", numericLit, ")") ^^ {a =>
    Universe(a.toInt)
  } | keyword("type") ^^ { _ => Universe(0) }

  lazy val let: PackratParser[Let] = delimited("{", rep(declaration) ~ term, "}") ^^ { a => Let(a._1, a._2)}

  lazy val teleInner =  rep1sep(opt(rep1(ident)) ~  (":" ~> term), ",") ^^ {
    a => a.map(a => NameType(a._1.getOrElse(Seq.empty).map(a => Name(Text(a))), a._2)) }

  lazy val tele: PackratParser[Seq[NameType]] = delimited("(", teleInner, ")")

  //        Primitives.keys.foldLeft[PackratParser[Term]](split) { (p, n) =>
  //          p | (keyword(n) ^^ {_ =>  Primitive(n) })
  //        } |

  lazy val term: PackratParser[Term] =
        let |
        pi |
        ascription |
        lambda |
        patternLambda |
        app |
        pathType |
        record |
        projection |
        sum |
        coe | com | hcom |
        universe |
        delimited("(", term, ")") |
        absDimension |
        ident ^^ {a => Reference(a)}

  // path type
  lazy val pathType: PackratParser[PathType] = term ~ ("≡" ~> opt(delimited("(", term ,")")) ~ term) ^^ {a =>
    PathType(a._2._1, a._1, a._2._2)
  }

  lazy val absDimension: PackratParser[Term] = numericLit  ^^ { i => Term.ConstantDimension(if (i == "0") false else if (i == "1") true else throw new Exception("...")) }

  // kan
  lazy val coe: PackratParser[Term] = keyword("coe") ~> delimited("(", term ~ delimited(",", term, ",") ~ term ~ ("," ~> term), ")")  ^^ {a => {
    Coe(DimensionPair(a._1._1._1, a._1._1._2), a._1._2, a._2)
  }}

  lazy val restriction: PackratParser[Term.Restriction] = ("|" ~> term <~ "=") ~ (term <~ "→") ~ term ^^ {a => Restriction(DimensionPair(a._1._1, a._1._2), a._2) }

  lazy val hcom: PackratParser[Term] = keyword("hcom") ~> (("(" ~> term) ~ delimited(",", term, ",") ~ term)  ~ delimited(",", atomicPattern ~ rep(restriction) ,")") ^^ { a =>
    Hcom(DimensionPair(a._1._1._1, a._1._1._2), a._1._2, a._2._1, a._2._2)
  }

  lazy val com: PackratParser[Term] = keyword("com") ~> delimited("(", term ~ delimited(",", term , ",") ~ term ~ ("," ~> term),",")  ~  (atomicPattern ~ rep(restriction) <~")") ^^ { a =>
    Com(DimensionPair(a._1._1._1._1, a._1._1._1._2), a._1._1._2, a._1._2, a._2._1, a._2._2)
  }

  // normal
  lazy val ascription: PackratParser[Cast] = delimited("(", (term <~ keyword("as")) ~ term, ")") ^^ {a => Cast(a._1, a._2)}

  lazy val pi: PackratParser[Function] = tele ~ ("⇒" ~> term) ^^ {a => Function(a._1, a._2)} |
    (term <~ "⇒") ~ term ^^ { a => Function(Seq(NameType(Seq.empty, a._1)), a._2)}

  lazy val atomicPattern: PackratParser[Name.Opt] = "─" ^^ {_ => None: Option[Name]} | ident ^^ { a =>
    Some(Name(Text(a)))
  }


  lazy val lambda: PackratParser[Lambda] = atomicPattern ~ ("→" ~> term) ^^ {a => Lambda(a._1, a._2) }

  lazy val groupPattern: PackratParser[Pattern] =  delimited("(", rep1sep(pattern, ","),")") ^^ { a => Pattern.Group(a) }

  lazy val namedPattern: PackratParser[Pattern] =
    ident ~ delimited("(", rep1sep(pattern, ","),")") ^^ { a => Pattern.NamedGroup(Text(a._1), a._2) }

  lazy val pattern: PackratParser[Pattern] = namedPattern | atomicPattern ^^ { a => Pattern.Atom(a) } | groupPattern

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

  lazy val app: PackratParser[App] = term ~ delimited("(", repsep(term, ","), ")") ^^ {a => App(a._1, a._2)}


  lazy val record: PackratParser[Record] = keyword("record") ~> delimited("{", rep(((keyword("field") ~> rep1(ident) <~ ":") ~ term) ^^ {a => NameType(a._1.map(k => Name(Text(k))), a._2)}), "}") ^^ {a => Record(a) }

  lazy val projection: PackratParser[Projection] = (term <~ ".") ~ ident ^^ {a => Projection(a._1, a._2)}

  lazy val sum: PackratParser[Sum] =
    (keyword("sum") ~> delimited("{", rep(
      (keyword("case") ~> ident ~ tele ^^ { a => Seq(Term.Constructor(a._1, a._2)) }) |
      (keyword("case") ~> rep1(ident) ^^ { _.map(i => Term.Constructor(Text(i), Seq.empty)) : Seq[Term.Constructor] })
    ),"}")) ^^ { a =>
      Sum(a.flatten)
    }


  def parse(a: String): ParseResult[Module] = (rep(declaration) ^^ { a=> Module(a) })(new PackratReader(new lexical.Scanner(a)))
}