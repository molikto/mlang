package mlang.core.checker

import java.util.concurrent.atomic.AtomicLong


trait GenericGen {
  def apply(): Generic
}

object GenericGen {
  object Positive extends GenericGen  {
    private val con= new AtomicLong(1)
    override def apply(): Generic = con.getAndIncrement()
  }

  object Negative extends GenericGen {
    private val abs = new AtomicLong(-1)
    override def apply(): Generic = abs.getAndDecrement()
  }
}
