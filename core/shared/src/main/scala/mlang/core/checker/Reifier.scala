package mlang.core.checker

trait Reify extends Context {


  def reify(v: Value): Abstract
}
