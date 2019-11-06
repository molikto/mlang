package mlang.compiler

import mlang.compiler.semantic.given
import mlang.compiler.semantic.Value
import mlang.compiler.dbi.{Abstract, DependencyType, Dependency}
import mlang.compiler.dbi.given
import mlang.utils._
import scala.collection.mutable

trait Holder {
  def value(vs: Array[Any]): Value
}


import org.objectweb.asm._
import Opcodes._

class MethodRun(val mv: MethodVisitor) {
  export mv._
  def lookup(d: Dependency): Int = ???
  def put(d: Dependency, i: Int): Unit = ???
}
object ByteCodeGeneratorRun {

  private val descriptors = mutable.Map[String, String]()
  private val clzgen = new GenLong.Positive()
  private val closureBootstrapHandle = new Handle(
    Opcodes.H_INVOKESTATIC,
    "java/lang/invoke/LambdaMetafactory",
    "metafactory",
    "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;",
    false
  )

  private val closureBootstrapArgs0 = Seq(
    Type.getType("()Ljava/lang/Object;"),
    Type.getType("(Ljava/lang/Object;)Ljava/lang/Object;"),
    Type.getType("(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"),
    Type.getType("(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;")
  )

  // inline def (mv: MethodVisitor) create[T <: Value](args: Any*): Unit = {
  //}

  private def (d: DependencyType) descriptor = d match {
    case DependencyType.Formula => "Lmlang/compiler/semantic/Formula;"
    case _ => "Lmlang/compiler/semantic/Value;"
  }
}
class ByteCodeGeneratorRun(val root: Abstract) {
  import ByteCodeGeneratorRun._
  import org.objectweb.asm._
  import Opcodes._

  private val visitedInnerClasses = mutable.Set[String]()
  private val mtdgen = new GenLong.Positive()
  private val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS)
  private val rootClzName = s"mlang/generated${clzgen()}"
  cw.visit(V12, ACC_SUPER, rootClzName, null, "java/lang/Object", Array("mlang/compiler/Holder"))
  cw.visitInnerClass("java/lang/invoke/MethodHandles$Lookup", "java/lang/invoke/MethodHandles", "Lookup", ACC_PUBLIC | ACC_FINAL | ACC_STATIC);

  private def visitMethod(name: String, des: String): MethodRun =
    new MethodRun(cw.visitMethod(ACC_PUBLIC, name, des, null, null))

  {
    val mv = cw.visitMethod(0, "<init>", "()V", null, null)
    mv.visitCode()
    mv.visitVarInsn(ALOAD, 0)
    mv.visitMethodInsn(INVOKESPECIAL, "java/lang/Object", "<init>", "()V", false)
    mv.visitInsn(RETURN)
    mv.visitMaxs(0, 0)
    mv.visitEnd()
  }


  private val deps = root.dependencies(0).toSeq

  def emit(): (Holder, Seq[Dependency]) = {
    (null, deps)
  }

  {
    val mv = visitMethod("value", "([Ljava/lang/Object;)Lmlang/compiler/semantic/Value;")
    mv.visitCode()
    // frame 0: this, 1: args
    // expand args
    mv.emit(root, 0)
    mv.visitInsn(ARETURN)
    mv.visitMaxs(0, 0)
    mv.visitEnd()
  }

  inline def (mv: MethodRun) emit(l: Int): Unit = {
    if (l == 0) mv.visitInsn(ICONST_0)
    else if (l == 1) mv.visitInsn(ICONST_1)
    else mv.visitLdcInsn(l)
  }

  inline def (mv: MethodRun) create(name: String): Unit = {
    val ds = ByteCodeGeneratorRun.descriptors
    val clzName = "mlang/compiler/semantic/Value$" + name
    val desc = ds.get(name) match {
      case Some(a) => a
      case None =>
        val method = java.lang.Class.forName(clzName).getMethod("apply")
        val a = mlang.utils.Runtime.getMethodDescriptor(method)
        ds.put(name, a)
        a
    }
    if (!visitedInnerClasses.contains(name)) {
      cw.visitInnerClass(clzName, "mlang/compiler/semantic/Value", name, ACC_PUBLIC | ACC_STATIC)
      visitedInnerClasses.add(name)
    }
    mv.visitMethodInsn(INVOKESTATIC, clzName, "apply", desc, false)
  }


  /**
  how do we translate a closure to invoke dynamic?
  first, given the closure, we need to find out all the captured variables, 
  and they are all in current frame!
  */
  private inline def (mv: MethodRun) closureBase(
    closure: dbi.Closure,
    args: Seq[dbi.DependencyType],
    selfDesSize: Int,
    selfDes: String,
    selfFunctionN: Int,
    depth: Int
  ): Unit = {
    // load captured local variables to stack
    // create the "function object"
    val captured = closure.dependencies(0)
    val name = s"closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val mthDesp = s"($capturedDes$selfDes)Lmlang/compiler/semantic/Value;" // captured variables + self variables => return type
    val mn = visitMethod(name, mthDesp)
    mn.visitCode()
    // stack: captured variables, parameters (maybe in seq form), 
    // transform stack by expanding parameters

    // put meta variables in local variables

    mn.emit(closure.term, depth + 1)
    mn.visitInsn(ARETURN)
    mn.visitMaxs(0, 0)
    mn.visitEnd()
    mv.visitInvokeDynamicInsn(
      "apply", 
      s"($capturedDes)Ldotty/runtime/function/JFunction${selfFunctionN};", 
      closureBootstrapHandle,
      Array[Object](
        closureBootstrapArgs0(selfDesSize),
        new Handle(
          Opcodes.H_INVOKESTATIC,
          rootClzName,
          name,
          mthDesp,
          false
        ),
        Type.getType(s"($selfDes)Lmlang/compiler/semantic/Value;") // self variables => return type
      )
    )
  }

  private def (mv: MethodRun) emitClosure(c: dbi.Closure, depth: Int): Unit = {

  }

  private def (mv: MethodRun) emit(term: Abstract, depth: Int): Unit = {
    // LATER we might be able to macro/typeclass it, but i don't have time, compared to moving away form Scala code generation
    term match {
      case Abstract.Universe(l) =>
        mv.emit(l)
        mv.create("Universe")
      case Abstract.App(left, right) =>
        mv.emit(left, depth)
        mv.emit(right, depth)
        mv.create("App")
      case Abstract.Lambda(closure) =>
        mv.emitClosure(closure, depth)
        mv.create("Lambda")
    }
  }

}

trait PlatformEvaluator extends Evaluator {

  protected def platformEval(term: Abstract): Value = {
    val (hd, ds) = new ByteCodeGeneratorRun(term).emit()
    ???
  }
}
