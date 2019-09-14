package mlang.compiler

import java.util.concurrent.atomic.AtomicLong

import mlang.utils._

import scala.util.Random

object GenName {

  private val abs = new AtomicLong(1)
  def apply(): Name = Name(Text(
    Random.alphanumeric.take(6).mkString("")
  ))
}
