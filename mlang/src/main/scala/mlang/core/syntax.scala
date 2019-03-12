package mlang.core

enum Term {
  case PositionalReference(depth: Int)
  case NamedReference()
  case Pi(from: Term, to: Term)
  case Lambda(from: Term, to: Term)
  case Application(left: Term, right: Term)
}