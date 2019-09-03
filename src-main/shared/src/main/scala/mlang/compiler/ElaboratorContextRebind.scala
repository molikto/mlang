package mlang.compiler


case class RebindNotFoundException() extends Exception

trait ElaboratorContextRebind extends ElaboratorContextBase {

  def rebindReference(v: Value.Reference): Option[Abstract.Reference] = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.Reference= null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case d: Layer.Defines =>
          var ll = d.terms
          while (ll.nonEmpty && binder == null) {
            if (ll.head.isDefined && ll.head.ref0.get.value.eq(v.value)) {
              index = i
              binder = Abstract.Reference(up, index)
            }
            i += 1
            ll = ll.tail
          }
        case _ =>
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    Option(binder)
  }


  def rebindFormula(a: Value.Formula): Abstract.Formula = {
    a match {
      case Value.Formula.Generic(stuck) =>
        rebindDimension(stuck)
      case Value.Formula.True => Abstract.Formula.True
      case Value.Formula.False => Abstract.Formula.False
      case Value.Formula.And(a, b) => Abstract.Formula.And(rebindFormula(a), rebindFormula(b))
      case Value.Formula.Or(a, b) => Abstract.Formula.Or(rebindFormula(a), rebindFormula(b))
      case Value.Formula.Neg(a) => Abstract.Formula.Neg(rebindFormula(a))
      case _: Value.Formula.Internal => logicError()
    }
  }

  def rebindDimension(id: Long): Abstract.Formula.Reference = {
    var up = 0
    var ls = layers
    var binder: Abstract.Formula.Reference = null
    while (ls.nonEmpty && binder == null) {
      ls.head match {
        case d: Layer.Dimension =>
          if (d.id == id) {
            binder = Abstract.Formula.Reference(up)
          }
        case _ =>
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    if (binder == null) {
      throw RebindNotFoundException()
    } else {
      binder
    }
  }

  def containsGeneric(id: Long): Boolean = {
    rebindGeneric0(id) != null
  }

  def rebindGeneric(id: Long): Abstract.Reference = {
    val binder = rebindGeneric0(id)
    if (binder == null) {
      throw RebindNotFoundException()
    } else {
      binder
    }
  }

  private def rebindGeneric0(id: Long): Abstract.Reference = {
    var up = 0
    var index = -1
    var ls = layers
    var binder: Abstract.Reference = null
    while (ls.nonEmpty && binder == null) {
      var i = 0
      ls.head match {
        case t: Layer.Parameters =>
          var ll = t.binders
          while (ll.nonEmpty && binder == null) {
            if (ll.head.id == id) {
              index = i
              binder = Abstract.Reference(up, index)
            }
            i += 1
            ll = ll.tail
          }
        case t: Layer.Defines =>
          var ll = t.terms
          while (ll.nonEmpty && binder == null) {
            if (!ll.head.isDefined) {
              if (ll.head.id == id) {
                index = i
                binder = Abstract.Reference(up, index)
              }
            }
            i += 1
            ll = ll.tail
          }
        case p:Layer.Parameter =>
          if (p.binder.id == id) {
            index = i
            binder = Abstract.Reference(up, -1)
          }
        case _ =>
      }
      if (binder == null) {
        ls = ls.tail
        up += 1
      }
    }
    binder
  }

}
