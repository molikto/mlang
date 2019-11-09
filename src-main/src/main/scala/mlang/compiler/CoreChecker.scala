package mlang.compiler

import dbi.Abstract
import semantic.Value
import mlang.utils._


case class CoreCheckFailedException() extends CompilerException

// very very simple and non-complete checker!!
trait CoreChecker extends ElaboratorContextBuilder
  with ElaboratorContextLookup
  with ElaboratorContextRebind
  with ElaboratorContextForEvaluator
  with DebugPrettyPrinter
  with semantic.ValueConversion
  with Evaluator {

  type Self  <: CoreChecker
  // FIXME this also seems support solving meta??

  def infer(abs: Abstract): Value = {
    abs match {
      case Abstract.Universe(i) =>
        Value.Universe.suc(i)
      // case Abstract.Function(d, i, co) =>
      //   infer(d) match {
      //     case Value.Universe(a) =>
      //       val (ctx, gen) = newParameterLayer(Name.empty, eval(d))
      //       ctx.infer(Abstract.App(Abstract.Path))
      //     case _ => throw CoreCheckFailedException()
      //   }
      case Abstract.Reference(up, index) =>
        getReferenceType(up, index)
      case Abstract.PathApp(a, b) =>
        infer(a).whnf match {
          case Value.PathType(ty, _, _) =>
            ty(eval(b))
          case _ => throw CoreCheckFailedException()
        }
      case Abstract.App(a, b) =>
        infer(a).whnf match {
          case Value.Function(d, i, co) =>
            co(eval(b))
          case _ => throw CoreCheckFailedException()
        }
      // case Abstract.MetaReference(up, index) =>
      //   getMetaReferenceType(up, index)
    }
  }

  def check(abs: Abstract, to: Value): Unit = {
    (abs, to.whnf) match {
      case _ => 
        if (!subTypeOf(infer(abs), to)) {
          throw CoreCheckFailedException()
        }
    }
  }
}