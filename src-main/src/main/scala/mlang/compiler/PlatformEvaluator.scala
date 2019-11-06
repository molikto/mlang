package mlang.compiler

import mlang.compiler.semantic.{given, _}
import mlang.utils._
import scala.collection.mutable
import scala.quoted._
import mlang.compiler.dbi.{Abstract}

trait Holder {
  def value(vs: Array[Any]): Value
}


private val clzgen = new GenLong.Positive()


// inline def (mv: MethodVisitor) create[T <: Value](args: Any*): Unit = {
//}


object ByteCodeGeneratorRun {
  private val descriptors = mutable.Map[String, String]()
}
class ByteCodeGeneratorRun(val root: Abstract) {
  import org.objectweb.asm._
  import Opcodes._

  private val visitedInnerClasses = mutable.Set[String]()
  private val mtdgen = new GenLong.Positive()
  val cw = new ClassWriter(ClassWriter.COMPUTE_MAXS)
  val rootClzName = s"mlang/generated${clzgen()}"
  cw.visit(V12, ACC_SUPER, rootClzName, null, "java/lang/Object", Array("mlang/compiler/Holder"))
  cw.visitInnerClass("java/lang/invoke/MethodHandles$Lookup", "java/lang/invoke/MethodHandles", "Lookup", ACC_PUBLIC | ACC_FINAL | ACC_STATIC);

  {
    val mv = cw.visitMethod(0, "<init>", "()V", null, null)
    mv.visitCode()
    mv.visitVarInsn(ALOAD, 0)
    mv.visitMethodInsn(INVOKESPECIAL, "java/lang/Object", "<init>", "()V", false)
    mv.visitInsn(RETURN)
    mv.visitMaxs(0, 0)
    mv.visitEnd()
  }

  {
    val mv = cw.visitMethod(ACC_PUBLIC, "value", "([Ljava/lang/Object;)Lmlang/compiler/semantic/Value;", null, null)
    mv.visitCode()
    mv.emit(root, -1)
    mv.visitInsn(ARETURN)
    mv.visitMaxs(0, 0)
    mv.visitEnd()
  }

  inline def (mv: MethodVisitor) emit(l: Int): Unit = {
    if (l == 0) mv.visitInsn(ICONST_0)
    else if (l == 1) mv.visitInsn(ICONST_1)
    else mv.visitLdcInsn(l)
  }

  inline def (mv: MethodVisitor) create(name: String): Unit = {
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


  private val closureBootstrapHandle = new Handle(
    Opcodes.H_INVOKESTATIC,
    "java/lang/invoke/LambdaMetafactory",
    "metafactory",
    "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;",
    false
  )
  private val closureBootstrapArgs0 = Type.getType("(Ljava/lang/Object;)Ljava/lang/Object;")
  /**
  how do we translate a closure to invoke dynamic?
  first, given the closure, we need to find out all the captured variables, 
  and they are all in current frame!
  */
  def (mv: MethodVisitor) emit(closure: Closure, depth: Int): Unit = {
    // load captured local variables to stack
    // create the "function object"
    mv.visitInvokeDynamicInsn(
      "apply", 
      "(Lmlang/compiler/semantic/Value;)Ldotty/runtime/function/JFunction1;", // captured variables => JFunction1
      closureBootstrapHandle,
      Array[Object](
        closureBootstrapArgs0,
        new Handle(
          Opcodes.H_INVOKESTATIC,
          rootClzName,
          "value$$anonfun$1",
          "(Lmlang/compiler/semantic/Value;)Lmlang/compiler/semantic/Value;", // captured variables + self variables => return type
          false
        ),
        Type.getType("(Lmlang/compiler/semantic/Value;)Lmlang/compiler/semantic/Value;") // self variables => return type
      )
    )
  }

  def (mv: MethodVisitor) emit(term: Abstract, depth: Int): Unit = {
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
        //mv.emit(closure, depth)
        mv.create("Lambda")
    }
  }

}

trait PlatformEvaluator extends Evaluator {

  protected def platformEval(term: Abstract): Value = {
    ???
  }
}
