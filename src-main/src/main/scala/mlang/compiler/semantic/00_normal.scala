package mlang.compiler.semantic


trait Normal[T] {
  def (a: T) nf: T
}