package mlang.compiler

import java.util.concurrent.atomic.AtomicLong


trait GenLong {
  def apply(): Long
}

object GenLong {
  class Positive extends GenLong  {
    private val con= new AtomicLong(1)
    override def apply(): Long = con.getAndIncrement()
  }

  object Negative {
    val gen = new Negative()
    val dgen = new Negative()
  }
  class Negative extends GenLong {
    private val abs = new AtomicLong(-1)
    override def apply(): Long = abs.getAndDecrement()
  }
}
