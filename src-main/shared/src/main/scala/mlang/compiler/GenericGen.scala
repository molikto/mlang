package mlang.compiler

import java.util.concurrent.atomic.AtomicLong


trait LongGen {
  def apply(): Long
}

object LongGen {
  class Positive extends LongGen  {
    private val con= new AtomicLong(1)
    override def apply(): Long = con.getAndIncrement()
  }

  object Negative {
    val gen = new Negative()
    val dgen = new Negative()
  }
  class Negative extends LongGen {
    private val abs = new AtomicLong(-1)
    override def apply(): Long = abs.getAndDecrement()
  }
}
