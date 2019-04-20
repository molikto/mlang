package mlang.core

import java.util.concurrent.atomic.AtomicLong


trait GenericGen {
  def apply(): Generic
}

object GenericGen {
  class Positive extends GenericGen  {
    private val con= new AtomicLong(1)
    override def apply(): Generic = con.getAndIncrement()
  }

  class Negative extends GenericGen {
    private val abs = new AtomicLong(-1)
    override def apply(): Generic = abs.getAndDecrement()
  }
}
