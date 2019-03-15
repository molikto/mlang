package mlang.utils


opaque type Unicode = String

object Unicode {
  def apply(str: String): Unicode = str
  
  def apply(i: Int): Unicode = i.toString

}
