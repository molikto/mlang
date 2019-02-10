package c_surface_syntax

import java.util.concurrent.atomic.AtomicLong


// surface syntax...
object surface {
  sealed trait Surface
  sealed trait Term
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

  // TODO better handle this!
  val letId = "not_used_let"
}


