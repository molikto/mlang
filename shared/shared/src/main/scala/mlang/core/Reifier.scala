package mlang.core

trait Reify extends Context {


  def reify(v: Value): Abstract
}
