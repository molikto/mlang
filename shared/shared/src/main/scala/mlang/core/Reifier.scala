package mlang.core

trait Reifier extends Context {


  def reify(v: Value): Abstract

  def reify(v: Value.Closure): Abstract
}
