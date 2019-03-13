package mlang.syntax

import mlang.utils._

// surface syntax is a **equivalence** of what user write, now is not complicated, wait for the editor

enum Term {
  case Let(defs: Seq[(Unicode, Term)], body: Term)
  case Ascription(term: Term, right: Term)
  case Pi(name: Option[Unicode], domain: Term, body: Term)
  case Lambda(name: Unicode, domain: Option[Term], body: Term)
  case CaseLambda(domain: Option[Term], cases: Seq[(Unicode, Option[Seq[Unicode]], Term)])
  case App(left: Term, right: Seq[Term])
  case Record(seq: Seq[(Unicode, Term)])
  case Make(term: Term, seq: Seq[(Unicode, Term)])
  case Projection(term: Term, str: Unicode)
  case Inductive(ts: Seq[(Unicode, Seq[(Unicode, Term)])])
  case Construct(ty: Term, name: Unicode, v: Option[Seq[Term]])
  case Reference(t: String)
  case Absent
}

