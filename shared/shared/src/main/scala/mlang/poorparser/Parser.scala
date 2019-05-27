package mlang.poorparser


import java.io.File

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
// TODO local match and local tree split syntax. give a more uniform syntax for lambda and patterns.
trait Parser extends StandardTokenParsers with PackratParsers with ImplicitConversions {






  override val lexical: StdLexical = new StdLexical {
    override def whitespaceChar: Parser[Char] = elem("", _ == '│') | super.whitespaceChar
  }

  lexical.reserved ++= List("define", "declare", "const_projections", "case", "__debug", "as", "coe", "hcom", "com","field", "ignored", "match", "record", "type", "sum", "inductively", "run", "with_constructors", "I", "_")
  lexical.delimiters ++= List("{", "}", "[", "]", ":", ",", "(", ")", "#", "≡", "─", "┬", "┌", "⊏", "└", "├", "⇒", "→", "+", "-", ";", "=", "@", "\\", ".", "|", "^")

  def delimited[T](a: String, t: Parser[T], b: String): Parser[T] = a ~> t <~ b


  lazy val declaration: PackratParser[Declaration] =declare |  define

  lazy val defineModifiers: PackratParser[Seq[Declaration.Modifier]] =
    rep(
      keyword("inductively") ^^ { _ => Declaration.Modifier.Inductively : Declaration.Modifier } |
      keyword("with_constructor") ^^ { _ => Declaration.Modifier.WithConstructor} |
      keyword("__debug") ^^ { _ => Declaration.Modifier.__Debug }
    )

  lazy val define: PackratParser[Declaration.Define] = (keyword("define") ~> defineModifiers ~ ident) ~ opt(tele) ~ opt(":" ~> term) ~ ("=" ~> term) ^^ { a =>
    Declaration.Define(a._1._1._1._1, Name(Text(a._1._1._1._2)), a._1._1._2.getOrElse(Seq.empty), a._1._2, a._2)
  }

  lazy val declare: PackratParser[Declaration.Declare] = (keyword("declare") ~> defineModifiers ~ ident) ~ opt(tele) ~ (":" ~> term) ^^ { a =>
    Declaration.Declare( a._1._1._1, Name(Text(a._1._1._2)), a._1._2.getOrElse(Seq.empty), a._2)
  }


  lazy val universe: PackratParser[Universe] = rep1("^") ~ keyword("type") ^^ {a =>
    Universe(a._1.size)
  } | keyword("type") ^^ { _ => Universe(0) }

  lazy val up: PackratParser[Term] = rep1("^") ~ ident ^^ { a => Up(Reference(a._2), a._1.size) }

  lazy val let: PackratParser[Let] = keyword("run") ~> delimited("{", rep(declaration) ~ term, "}") ^^ { a => Let(a._1, a._2)}

  lazy val teleInner =  rep1sep(opt(rep1(nonEmptyImplicitPattern)) ~  (":" ~> term), ",") ^^ {
    a => a.map(a => NameType(a._1.getOrElse(Seq.empty), a._2)) }

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
        record | interval |
        projection |
        meta |
        sum |
        up |
        coe | com | hcom |
        universe |
        delimited("(", term, ")") |
        absDimension |
        ident ^^ {a => Reference(a)}

  lazy val meta: PackratParser[Term] = keyword("_") ^^ {_ => Hole }

  lazy val interval: PackratParser[Term] = keyword("I") ^^ { _ => I }
  // path type
  lazy val pathType: PackratParser[PathType] = term ~ ("≡" ~> opt(delimited("[", term ,"]")) ~ term) ^^ {a =>
    PathType(a._2._1, a._1, a._2._2)
  }

  lazy val absDimension: PackratParser[Term] = numericLit  ^^ { i => Term.ConstantDimension(if (i == "0") false else if (i == "1") true else throw new Exception("...")) }

  // kan
  lazy val coe: PackratParser[Term] = keyword("coe") ~> delimited("(", term ~ delimited(",", term, ",") ~ term ~ ("," ~> term), ")")  ^^ {a => {
    Coe(Pair(a._1._1._1, a._1._1._2), a._1._2, a._2)
  }}

  lazy val face: PackratParser[Term.Face] = ("|" ~> term <~ "=") ~ (term <~ "→") ~ term ^^ {a => Face(Pair(a._1._1, a._1._2), a._2) }

  lazy val hcom: PackratParser[Term] = keyword("hcom") ~> (("(" ~> term) ~ delimited(",", term, ",") ~ term)  ~ delimited(",", atomicPattern ~ rep(face) ,")") ^^ { a =>
    Hcom(Pair(a._1._1._1, a._1._1._2), a._1._2, a._2._1, a._2._2)
  }

  lazy val com: PackratParser[Term] = keyword("com") ~> delimited("(", term ~ delimited(",", term , ",") ~ term ~ ("," ~> term),",")  ~  (atomicPattern ~ rep(face) <~")") ^^ { a =>
    Com(Pair(a._1._1._1._1, a._1._1._1._2), a._1._1._2, a._1._2, a._2._1, a._2._2)
  }

  // normal
  lazy val ascription: PackratParser[Cast] = delimited("(", (term <~ keyword("as")) ~ term, ")") ^^ {a => Cast(a._1, a._2)}

  lazy val pi: PackratParser[Function] = tele ~ ("⇒" ~> term) ^^ {a => Function(a._1, a._2)} |
    (term <~ "⇒") ~ term ^^ { a => Function(Seq(NameType(Seq.empty, a._1)), a._2)}
  
  lazy val nonEmptyAtomicPattern: PackratParser[Name] = ident ^^ { a =>
    Name(Text(a))
  }
  
  lazy val nonEmptyImplicitPattern: PackratParser[(Boolean, Name)] = (opt("#") ~ nonEmptyAtomicPattern) ^^ {a => (a._1.isDefined, a._2) }

  lazy val atomicPattern: PackratParser[Name] = "─" ^^ {_ => Name.empty } | nonEmptyAtomicPattern

  lazy val implicitPattern: PackratParser[(Boolean, Name)] = (opt("#") ~ atomicPattern) ^^ {a => (a._1.isDefined, a._2) }


  lazy val lambda: PackratParser[Lambda] =
    implicitPattern ~ ("→" ~> term) ^^ {a => Lambda(a._1._2, a._1._1, a._2) }

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

  lazy val patternCases: PackratParser[PatternLambda] = opt("#") ~ (patternCaseEmpty | patternCaseSingle | patternMultiple) ^^ {
    a => PatternLambda(a._1.isDefined, a._2)
  }
  lazy val patternLambda : PackratParser[Term] =  "─" ~> patternContinue ^^ { a => Term.Lambda(Name.empty, false, a) } |  patternCases

  lazy val app: PackratParser[App] = term ~ delimited("(", repsep(opt("#") ~ term, ","), ")") ^^ {a => App(a._1, a._2.map(k => (k._1.isDefined, k._2)))}


  lazy val record: PackratParser[Record] = keyword("record") ~> delimited("{", rep(((keyword("field") ~> rep1(nonEmptyImplicitPattern) <~ ":") ~ term) ^^ {a => NameType(a._1, a._2)}), "}") ^^ {a => Record(a) }

  lazy val projection: PackratParser[Projection] = (term <~ ".") ~ ident ^^ {a => Projection(a._1, a._2)}

  lazy val sum: PackratParser[Sum] =
    (keyword("sum") ~> delimited("{", rep(
      (keyword("case") ~> atomicPattern ~ tele ^^ { a => Seq(Term.Constructor(a._1, a._2)) }) |
      (keyword("case") ~> rep1(atomicPattern) ^^ { _.map(i => Term.Constructor(i, Seq.empty)) : Seq[Term.Constructor] })
    ),"}")) ^^ { a =>
      Sum(a.flatten)
    }

  def parse(a: String) = Benchmark.Parsing {
    (rep(declaration) ^^ { a=> Module(a) })(new PackratReader(new lexical.Scanner(a)))
  }

  def src(a: File): String = scala.io.Source.fromFile(a).getLines().mkString("\n")

  def parseOrThrow(a: String): Module = parse(a) match {
    case Success(result, next) =>
      if (next.atEnd) {
        result
      } else {
        throw new Exception("Parse failed with last " + result.declarations.lastOption + "and remaining " + next.rest.toString)
      }
    case NoSuccess(msg, _) =>
      throw new Exception(s"Parse failed with $msg")
  }

}