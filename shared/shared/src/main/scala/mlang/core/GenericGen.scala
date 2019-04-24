package mlang.core

import java.util.concurrent.atomic.AtomicLong


trait LongGen {
  def apply(): Long
}

object LongGen {
  class Positive extends LongGen  {
    private val con= new AtomicLong(1)
    override def apply(): Long = con.getAndIncrement()
  }

  class Negative extends LongGen {
    private val abs = new AtomicLong(-1)
    override def apply(): Long = abs.getAndDecrement()
  }
}
