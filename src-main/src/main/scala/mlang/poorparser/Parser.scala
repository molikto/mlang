package mlang.poorparser


import java.io.File
import java.util.concurrent.atomic.AtomicLong

import mlang.compiler.concrete._
import mlang.compiler.concrete.Concrete._

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.{ImplicitConversions, PackratParsers}
import mlang.utils.{Name, _}

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

  lexical.reserved ++= List("contextual_constructors", "without_define", "define", "declare", "const_projections", "parameters", "case", "__debug", "as", "transp", "hcomp", "comp", "hfill", "fill", "field", "ignored", "match", "record", "type", "sum", "inductively", "run", "with_constructors", "I", "_", "make", "glue_type", "glue", "unglue")
  lexical.delimiters ++= List("{", "}", "[", "]", ":", ",", "(", ")", "#", "≡", "─", "???", "┬", "┌", "⊏", "└", "├", "⇒", "→", "+", "-", ";", "=", "@", "\\", ".", "|", "^", "∨", "∧", "~")

  def delimited[T](a: String, t: Parser[T], b: String): Parser[T] = a ~> t <~ b


  lazy val declaration: PackratParser[Declaration] =  parameters | declare |  define

  lazy val defineModifiers: PackratParser[Seq[DeclarationModifier]] =
    rep(
      keyword("without_define") ^^ { _ => DeclarationModifier.WithoutDefine : DeclarationModifier } |
      keyword("inductively") ^^ { _ => DeclarationModifier.Inductively : DeclarationModifier } |
      keyword("with_constructor") ^^ { _ => DeclarationModifier.WithConstructor} |
      keyword("__debug") ^^ { _ => DeclarationModifier.__Debug }
    )

  lazy val define: PackratParser[Declaration.Define] = (keyword("define") ~> defineModifiers ~ ident) ~ opt(tele) ~ opt(":" ~> term) ~ ("=" ~> term) ^^ { a =>
    Declaration.Define(a._1._1._1._1, Name(Text(a._1._1._1._2)), a._1._1._2.getOrElse(Seq.empty), a._1._2, a._2)
  }

  lazy val parameters: PackratParser[Declaration] = (keyword("parameters") ~> tele ~ delimited("{", rep(declaration), "}")) ^^ { a =>
    Declaration.Parameters(a._1, a._2)
  }

  lazy val declare: PackratParser[Declaration.Declare] = (keyword("declare") ~> defineModifiers ~ ident) ~ opt(tele) ~ (":" ~> term) ^^ { a =>
    Declaration.Declare( a._1._1._1, Name(Text(a._1._1._2)), a._1._2.getOrElse(Seq.empty), a._2)
  }


  lazy val universe: PackratParser[Concrete] = keyword("type") ^^ { _ => Concrete.Type }

  lazy val up: PackratParser[Concrete] = rep1("^") ~ ( universe | reference ) ^^ { a => Up(a._2, a._1.size) }

  lazy val let: PackratParser[Let] = keyword("run") ~> delimited("{", rep(declaration) ~ term, "}") ^^ { a => Let(a._1, a._2)}

  lazy val teleInner =  rep1sep(opt(rep1(nonEmptyImplicitPattern)) ~  (":" ~> term), ",") ^^ {
    a => a.map(a => NameType(a._1.getOrElse(Seq.empty), a._2)) }

  lazy val tele: PackratParser[Seq[NameType]] = delimited("(", teleInner, ")")

  //        Primitives.keys.foldLeft[PackratParser[Term]](split) { (p, n) =>
  //          p | (keyword(n) ^^ {_ =>  Primitive(n) })
  //        } |

  lazy val term: PackratParser[Concrete] =
        let |
        pi |
        ascription |
        lambda |
        patternLambda |
        app |
        pathType |
        and | or | neg |
        record | interval | undefined |
        projection |
        meta |
        sum |
        up |
        transp | com | hcom | hfill | fill | glueType | glue | unglue |
        universe | make |
        delimited("(", term, ")") |
        number | reference

  lazy val reference = ident ^^ {a => Reference(Text(a)) }
  lazy val make: PackratParser[Concrete] = keyword("make") ^^ { _ => Make }
  lazy val meta: PackratParser[Concrete] = keyword("_") ^^ { _ => Hole }

  lazy val interval: PackratParser[Concrete] = keyword("I") ^^ { _ => I }

  lazy val and: PackratParser[Concrete] = ((term <~ "∧") ~ term) ^^ {a => And(a._1, a._2)}
  lazy val or: PackratParser[Concrete] = ((term <~ "∨") ~ term) ^^ {a => Or(a._1, a._2)}
  lazy val neg: PackratParser[Concrete] = ("~" ~> term) ^^ { a => Neg(a) }

  lazy val undefined: PackratParser[Concrete] = "???" ^^ { _ => Undefined }
  // path type
  lazy val pathType: PackratParser[PathType] = term ~ ("≡" ~> opt(delimited("[", term ,"]")) ~ term) ^^ {a =>
    PathType(a._2._1, a._1, a._2._2)
  }

  lazy val number: PackratParser[Concrete] = (numericLit ^^ { a => Concrete.Number(a) })

  // kan
  lazy val transp: PackratParser[Concrete] = keyword("transp") ~> delimited("(", (term <~ ",") ~ term ~ ("," ~> term), ")")  ^^ { a => {
    Transp(a._1._1, a._1._2, a._2)
  }}

  lazy val glueType: PackratParser[Concrete]=  keyword("glue_type") ~> ("(" ~> term) ~ (rep(face) <~ ")") ^^ { a =>
    GlueType(a._1, a._2)
  }

  lazy val glue: PackratParser[Concrete]=  keyword("glue") ~> ("(" ~> term) ~ (rep(face) <~ ")") ^^ { a =>
    Glue(a._1, a._2)
  }

   lazy val unglue: PackratParser[Concrete]= keyword("unglue") ~> ("(" ~> term) <~ (")") ^^ { a =>
      Unglue(a)
    }

//  lazy val unglue: PackratParser[Concrete]= keyword("unglue") ~> ("(" ~> term) ~ (rep(face) <~ ")") ^^ { a =>
//    Unglue(a._1, a._2)
//  }

  lazy val face: PackratParser[Face] = (("|" ~> term <~ ":") ~ term) ^^ { a => Face(a._1, a._2) }

  lazy val hcom: PackratParser[Concrete] = keyword("hcomp") ~> ("(" ~> term) ~ (rep(face) <~ ")") ^^ { a =>
    Hcomp(a._1, a._2)
  }

  val nameGen = new AtomicLong()
  def genName = Text("$" + nameGen.getAndIncrement())

  // FIXME these is really ugly!!!
  lazy val hfill: PackratParser[Concrete] = keyword("hfill") ~> ("(" ~> term) ~ (rep(face) <~ ")") ^^ { tttm =>
      val base = tttm._1
    val tfaces = tttm._2
    val ni = genName
    val nj = genName
    val face1 = Face(Neg(Reference(ni)), Lambda(Name.empty, false, false, base))
    val faces = tfaces.map(a => {
      val body = a.term match {
        case l: Lambda => l.copy(ensuredPath = true)
        case a => a
      }
      Face(a.dimension, Lambda(Name(nj), false, false, App(body, And(Reference(nj), Reference(ni)))))
    })
    Lambda(Name(ni), false, true, Hcomp(base, face1 +: faces))
  }

  lazy val fill: PackratParser[Concrete] = keyword("fill") ~>  delimited("(", term,",") ~ term  ~  (rep(face) <~")") ^^ { tttm =>
      val tp = tttm._1._1
    val base = tttm._1._2
    val tfaces = tttm._2
    val nt = genName
    val ni = genName
    val nj = genName
    val face1 = Face(Neg(Reference(ni)), Lambda(Name.empty, false, false, base))
    val faces = tfaces.map(a => {
      val body = a.term match {
        case l: Lambda => l.copy(ensuredPath = true)
        case a => a
      }
      Face(a.dimension, Lambda(Name(nj), false, false, App(body, And(Reference(nj), Reference(ni)))))
    })
    Lambda(Name(ni), false, true, Comp(Lambda(Name(nt), false, true, App(tp, And(Reference(ni), Reference(nt)))), base, face1 +: faces))
  }

  lazy val com: PackratParser[Concrete] = keyword("comp") ~> delimited("(", term,",") ~ term  ~  (rep(face) <~")") ^^ { a =>
    Comp(a._1._1, a._1._2, a._2)
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
    implicitPattern ~ ("→" ~> term) ^^ {a => Lambda(a._1._2, a._1._1, false, a._2) }

  lazy val groupPattern: PackratParser[Pattern] =  delimited("(", rep1sep((opt("#") ~ pattern) ^^ {a => (a._1.isDefined, a._2)}, ","),")") ^^ { a => Pattern.Group(a) }

  lazy val namedPattern: PackratParser[Pattern] =
    ident ~ delimited("(", rep1sep((opt("#") ~ pattern) ^^ {a => (a._1.isDefined, a._2)}, ","),")") ^^ { a => Pattern.NamedGroup(Text(a._1), a._2) }

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
  lazy val patternLambda : PackratParser[Concrete] =  "─" ~> patternContinue ^^ { a => Lambda(Name.empty, false, false, a) } |  patternCases

  lazy val app: PackratParser[App] = term ~ delimited("(", repsep(opt("@") ~ term, ","), ")") ^^ {a => App(a._1, a._2.map(k => (k._1.isDefined, k._2)))}

  lazy val record: PackratParser[Record] = keyword("record") ~> delimited("{", rep(((keyword("field") ~> rep1(nonEmptyImplicitPattern) <~ ":") ~ term) ^^ {a => NameType(a._1, a._2)}), "}") ^^ {a => Record(a) }

  lazy val projection: PackratParser[Projection] = (term <~ ".") ~ (make | reference) ^^ {a => Projection(a._1, a._2)}

  lazy val sum: PackratParser[Sum] =
    (keyword("sum") ~> opt(keyword("contextual_constructors")) ~ delimited("{", rep(
      (keyword("case") ~> atomicPattern ~ delimited("(", teleInner ~ rep(face),")") ^^ { a => Seq(Constructor(a._1, a._2._1, a._2._2)) }) |
      (keyword("case") ~> rep1(atomicPattern) ^^ { _.map(i => Constructor(i, Seq.empty, Seq.empty)) : Seq[Constructor] })
    ),"}")) ^^ { a =>
      Sum(a._1.isDefined, a._2.flatten)
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