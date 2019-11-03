package mlang.compiler.semantic

type Assignment = (Long, Boolean)
type Assignments = Set[Assignment]
object Assignments {
  def satisfiable(rs: Assignments): Boolean = rs.map(_._1).size == rs.size
}

sealed trait Formula {
  import Formula._
  def names: Set[Long] = {
    this match {
      case Generic(id) => if (id != 0) Set(id) else Set.empty // 0 is only used as a hack
      case True => Set.empty
      case False => Set.empty
      case And(left, right) => left.names ++ right.names
      case Or(left, right) => left.names ++ right.names
      case Neg(unit) => unit.names
    }
  }

  def normalFormTrue = normalForm == NormalForm.True

  def satisfiable: Boolean = NormalForm.satisfiable(normalForm)

  def normalForm: NormalForm  = {
    def merge(a: NormalForm, b: NormalForm): NormalForm = {
      def properSupersetOfAny(c: Assignments, g: NormalForm) = g.exists(g => g.subsetOf(c) && g != c)
      a.filter(c => !properSupersetOfAny(c, b)) ++ b.filter(c => !properSupersetOfAny(c, a))
    }
    this match {
      case True => NormalForm.True
      case False => NormalForm.False
      case Generic(id) => Set(Set((id, true)))
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

  def fswap(w: Long, z: Formula): Formula = (this match {
    case g:Generic => if (g.id == w) z else g
    case True => True
    case False => False
    case And(left, right) => And(left.fswap(w, z), right.fswap(w, z))
    case Or(left, right) => Or(left.fswap(w, z), right.fswap(w, z))
    case Neg(unit) => Neg(unit.fswap(w, z))
  }).simplify

  def restrict(lv: Assignments): Formula = if (lv.isEmpty) this else {
    val ret = this match {
      case g:Generic => g.assign(lv)
      case True => True
      case False => False
      case And(left, right) => And(left.restrict(lv), right.restrict(lv))
      case Or(left, right) => Or(left.restrict(lv), right.restrict(lv))
      case Neg(unit) => Neg(unit.restrict(lv))
    }
    ret.simplify
  }

  def simplify : Formula = this match {
    case g:Generic => g
    case True => True
    case False => False
    case And(left, right) =>
      val l = left.simplify
      val r = right.simplify
      if (l == True) {
        r
      } else if (r == True) {
        l
      } else if (l == False || r == False) {
        False
      } else {
        And(l, r)
      }
    case Or(left, right) =>
      val l = left.simplify
      val r = right.simplify
      if (l == False) {
        r
      } else if (r == False) {
        l
      } else if (l == True || r == True) {
        True
      } else {
        Or(l, r)
      }
    case Neg(unit) => unit.simplify match {
      case False => True
      case True => False
      case Neg(c) => c
      case a => Neg(a)
    }
  }

  def elim(i: Long): Formula = Formula(NormalForm.elim(normalForm, i))
}

object Formula {
  def apply(nf: NormalForm): Formula = {
    val ret = nf.foldLeft(False : Formula) {(f, z) =>
      Or(f, z.foldLeft(True : Formula) { (t, y) => And(t, if (y._2) Generic(y._1) else Neg(Generic(y._1)))})}
    ret.simplify
  }


  def phi(se: Iterable[Formula]) = se.flatMap(_.normalForm).toSet
  type NormalForm = Set[Assignments]
  object NormalForm {
    def elim(nf: NormalForm, value: Long) = nf.filter(!_.exists(_._1 == value))

    def satisfiable(_2: NormalForm): Boolean = _2.exists(Assignments.satisfiable)

    val True: NormalForm = Set(Set.empty)
    val False: NormalForm = Set.empty
  }
  case class Generic(id: Long) extends Formula {
    def assign(asgs: Assignments): Formula = asgs.find(_._1 == id) match {
      case Some(a) => if (a._2) True else False
      case None => this
    }
  }
  object True extends Formula
  object False extends Formula
  case class And(left: Formula, right: Formula) extends Formula
  object Or {
    def apply(fs: Iterable[Formula]): Formula = {
      fs.foldLeft(False: Formula) {
        (f, a) => Or(f, a)
      }
    }
  }
  case class Or(left: Formula, right: Formula) extends Formula
  case class Neg(unit: Formula) extends Formula
}

