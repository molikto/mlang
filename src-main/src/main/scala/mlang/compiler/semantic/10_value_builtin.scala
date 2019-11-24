package mlang.compiler.semantic

import mlang.utils._

object BuiltIn {
  var equiv: Value.GlobalReference = null
  var fiber_at: Value.GlobalReference = null
  var equiv_of: Value.GlobalReference = null
  var path_to_equiv: Value.GlobalReference = null

  def trySave(name: Name, ref: Value.GlobalReference): Boolean = {
    if (name == Name(Text("fiber_at"))) {
      assert(BuiltIn.fiber_at == null)
      BuiltIn.fiber_at = ref
      true
    } else if (name == Name(Text("equiv"))) {
      assert(BuiltIn.equiv == null)
      BuiltIn.equiv = ref
      true
    } else if (name == Name(Text("equiv_of"))) {
      assert(BuiltIn.equiv_of == null)
      BuiltIn.equiv_of = ref
      true
    } else if (name == Name(Text("path_to_equiv"))) {
      assert(BuiltIn.path_to_equiv == null)
      BuiltIn.path_to_equiv = ref
      true
    } else {
      false
    }
  }
}
