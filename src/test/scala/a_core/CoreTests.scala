package a_core

import utest._

object CoreTests extends TestSuite {

  val justId = Make(Seq(
    ValueDeclaration("id", Lambda(DeclarationReference(1, "type"), Lambda(VariableReference(0), VariableReference(0))))
  ))
  val tests = Tests {
    new TypeChecker().check(justId)
  }
}