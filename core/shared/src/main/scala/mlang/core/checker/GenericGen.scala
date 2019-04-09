package mlang.core.checker

import java.util.concurrent.atomic.AtomicLong


trait GenericGen {

  private val con= new AtomicLong(1)
  private val abs = new AtomicLong(-1)

  def generic(): Generic = con.getAndIncrement()
  def negativeGeneric(): Generic = abs.getAndDecrement()
}
