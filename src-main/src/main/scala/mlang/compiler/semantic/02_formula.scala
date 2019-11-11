package mlang.compiler.semantic

type Assignment = (Long, Boolean)

type Assignments = Set[Assignment]

given (rs: Assignments) {
  def satisfiable: Boolean = rs.map(_._1).size == rs.size
}

// LATER this is not a good name in this package. but I am so lazy to came up with good ones now
type NormalForm = Set[Assignments]
object NormalForm {
  val True: NormalForm = Set(Set.empty)
  val False: NormalForm = Set.empty
}
given (nf: NormalForm) {
  def elim(value: Long) = nf.filter(!_.exists(_._1 == value))
  def satisfiable: Boolean = nf.exists(_.satisfiable)
}


object Formula {
  case class Generic(id: Long) extends Formula {
    def assign(asgs: Assignments): Formula = asgs.find(_._1 == id) match {
      case Some(a) => if (a._2) True else False
      case None => this
    }
  }
  object True extends Formula
  object False extends Formula
  case class And(left: Formula, right: Formula) extends Formula
  case class Or(left: Formula, right: Formula) extends Formula
  object Or {
    def apply(fs: Iterable[Formula]): Formula = {
      fs.foldLeft(False: Formula) {
        (f, a) => Or(f, a)
      }
    }
  }
  case class Neg(unit: Formula) extends Formula

  def apply(nf: NormalForm): Formula = {
    val ret = nf.foldLeft(False : Formula) {(f, z) =>
      Or(f, z.foldLeft(True : Formula) { (t, y) => And(t, if (y._2) Generic(y._1) else Neg(Generic(y._1)))})}
    ret.simplify
  }
}

sealed trait Formula {
  import Formula._
  def names: Set[Long] = {
    this match {
      case Generic(id) => Set(id)
      case True => Set.empty
      case False => Set.empty
      case And(left, right) => left.names ++ right.names
      case Or(left, right) => left.names ++ right.names
      case Neg(unit) => unit.names
    }
  }

  def nfTrue = normalForm == NormalForm.True
  def nfFalse = normalForm == NormalForm.False

  def satisfiable: Boolean = normalForm.satisfiable

  def normalForm: NormalForm  = {
    def merge(a: NormalForm, b: NormalForm): NormalForm = {
      def properSupersetOfAny(c: Assignments, g: NormalForm) = g.exists(g => g.subsetOf(c) && g != c)
      a.filter(c => !properSupersetOfAny(c, b)) ++ b.filter(c => !properSupersetOfAny(c, a))
    }
    this match {
      case True => NormalForm.True
      case False => NormalForm.False
      case Generic(id) => Set(Set(id -> true))
      case And(left, right) =>
        val ln = left.normalForm.toSeq
        val rn = right.normalForm.toSeq
        ln.flatMap(i => rn.map(r => Set(i ++ r) : NormalForm)).foldLeft(NormalForm.False) { (a, b) => merge(a, b) }
      case Or(left, right) => merge(left.normalForm, right.normalForm)
      case Neg(unit) =>
        def negate(f: Formula): Formula = f match {
          case g: Generic => Neg(g)
          case And(left, right) => Or(negate(left), negate(right))
          case Or(left, right) => And(negate(left), negate(right))
          case Neg(u2) => u2
          case True => False
          case False => True
        }
        unit match {
          case Generic(id) => Set(Set((id, false)))
          case r => negate(r).normalForm
        }
    }
  }


  def simplify : Formula = this match {
    case g:Generic => g
    case True => True
    case False => False
    case And(left, right) =>
      val l = left.simplify
      val r = right.simplify
      if (l == True) r
      else if (r == True) l
      else if (l == False || r == False) False
      else And(l, r)
    case Or(left, right) =>
      val l = left.simplify
      val r = right.simplify
      if (l == False) r
      else if (r == False) l
      else if (l == True || r == True) True
      else Or(l, r)
    case Neg(unit) => unit.simplify match {
      case False => True
      case True => False
      case Neg(c) => c
      case a => Neg(a)
    }
  }

  def elim(i: Long): Formula = Formula(normalForm.elim(i))
}

def (se: Iterable[Formula]) phi: NormalForm =  se.flatMap(_.normalForm).toSet

given Nominal[Formula] {
  import Formula._

  def (f: Formula) supportShallow(): SupportShallow = SupportShallow(f.names, Set.empty)

  def (t: Formula) fswap(w: Long, z: Formula): Formula = (t match {
    case g:Generic => if (g.id == w) z else g
    case True => True
    case False => False
    case And(left, right) => And(left.fswap(w, z), right.fswap(w, z))
    case Or(left, right) => Or(left.fswap(w, z), right.fswap(w, z))
    case Neg(unit) => Neg(unit.fswap(w, z))
  }).simplify

  def (t: Formula) restrict(lv: Assignments): Formula = if (lv.isEmpty) t else {
    val ret = t match {
      case g:Generic => g.assign(lv)
      case True => True
      case False => False
      case And(left, right) => And(left.restrict(lv), right.restrict(lv))
      case Or(left, right) => Or(left.restrict(lv), right.restrict(lv))
      case Neg(unit) => Neg(unit.restrict(lv))
    }
    ret.simplify
  }
}