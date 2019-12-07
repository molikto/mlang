package mlang.compiler

import mlang.compiler.semantic.given
import mlang.compiler.semantic.Value
import mlang.compiler.dbi.{Abstract, DependencyType, Dependency}
import mlang.compiler.dbi.given
import mlang.utils._
import scala.collection.mutable
import mlang.utils.JavaRuntime

// TODO it seems this is slower than before in terms of compiled bytecode performance, which goes though Scala compiler. wait when Dotty has self compiler and port that one to here!
trait Holder {
  def value(vs: Array[Object]): Value
}


import org.objectweb.asm._
import Opcodes._

class MethodRun(val mv: MethodVisitor, val name: String = "") extends PlatformEvaluatorHelpers {
  export mv._
  val lookup = mutable.Map[Dependency, Int]()

  def diff(i: Int): MethodRun = {
    val a = new MethodRun(mv, name)
    for (l <- lookup) {
      a.lookup.put(l._1.diff(1), l._2)
    }
    a
  }
}

object ByteCodeGeneratorRun {

  private val descriptors = mutable.Map[String, String]()
  private val clzgen = new GenLong.Positive()
  private def closureBootstrapHandle = new Handle(
    Opcodes.H_INVOKESTATIC,
    "java/lang/invoke/LambdaMetafactory",
    "metafactory",
    "(Ljava/lang/invoke/MethodHandles$Lookup;Ljava/lang/String;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodType;Ljava/lang/invoke/MethodHandle;Ljava/lang/invoke/MethodType;)Ljava/lang/invoke/CallSite;",
    false
  )

  private val objs = mutable.ArrayBuffer[Object]()
  private def tunnel(a: Object): Int = {
    objs.insert(objs.size, a)
    objs.size - 1
  }

  def getPattern(i: Int): Pattern = {
    objs(i).asInstanceOf[Pattern]
  }

  def getETypeFunction(i: Int): EType.Function = {
    objs(i).asInstanceOf[EType.Function]
  }

  def getETypeSum(i: Int): EType.Sum = {
    objs(i).asInstanceOf[EType.Sum]
  }

  def getETypeRecord(i: Int): EType.Record = {
    objs(i).asInstanceOf[EType.Record]
  }

  def getName(i: Int): Name = {
    objs(i).asInstanceOf[Name]
  }

  private val closureBootstrapArgs0 = Seq(
    Type.getType("()Ljava/lang/Object;"),
    Type.getType("(Ljava/lang/Object;)Ljava/lang/Object;"),
    Type.getType("(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"),
    Type.getType("(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;")
  )

  val metaInitilizeSig = JavaRuntime.getMethodDescriptor(classOf[Value.Meta].getMethods.find(_.getName == "initialize").get)

  val localReferenceInitilizeSig = JavaRuntime.getMethodDescriptor(classOf[Value.LocalReference].getMethods.find(_.getName == "initialize").get)

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
  private val rootClzName = s"mlang_generated_${clzgen()}"
  cw.visit(V1_8, ACC_SUPER, rootClzName, null, "java/lang/Object", Array("mlang/compiler/Holder"))
  cw.visitInnerClass("java/lang/invoke/MethodHandles$Lookup", "java/lang/invoke/MethodHandles", "Lookup", ACC_PUBLIC | ACC_FINAL | ACC_STATIC)
  cw.visitInnerClass("mlang/compiler/semantic/Value$Meta", "mlang/compiler/semantic/Value", "Meta", ACC_PUBLIC | ACC_STATIC)
  cw.visitInnerClass("mlang/compiler/semantic/Value$Meta", "mlang/compiler/semantic/Value", "Meta", ACC_PUBLIC | ACC_STATIC)
  cw.visitInnerClass("scala/collection/immutable/ArraySeq$ofRef", "scala/collection/immutable/ArraySeq", "ofRef", ACC_PUBLIC | ACC_FINAL | ACC_STATIC);

  cw.visitInnerClass("mlang/compiler/semantic/Formula$And", "mlang/compiler/semantic/Formula", "And", ACC_PUBLIC | ACC_STATIC);
  cw.visitInnerClass("mlang/compiler/semantic/Formula$And$", "mlang/compiler/semantic/Formula", "And$", ACC_PUBLIC | ACC_FINAL | ACC_STATIC);
  cw.visitInnerClass("mlang/compiler/semantic/Formula$Neg", "mlang/compiler/semantic/Formula", "Neg", ACC_PUBLIC | ACC_STATIC);
  cw.visitInnerClass("mlang/compiler/semantic/Formula$Neg$", "mlang/compiler/semantic/Formula", "Neg$", ACC_PUBLIC | ACC_FINAL | ACC_STATIC);
  cw.visitInnerClass("mlang/compiler/semantic/Formula$Or", "mlang/compiler/semantic/Formula", "Or", ACC_PUBLIC | ACC_STATIC);
  cw.visitInnerClass("mlang/compiler/semantic/Formula$Or$", "mlang/compiler/semantic/Formula", "Or$", ACC_PUBLIC | ACC_FINAL | ACC_STATIC);
  cw.visitInnerClass("mlang/compiler/semantic/Formula$False$", "mlang/compiler/semantic/Formula", "False$", ACC_PUBLIC | ACC_FINAL | ACC_STATIC);
  cw.visitInnerClass("mlang/compiler/semantic/Formula$True$", "mlang/compiler/semantic/Formula", "True$", ACC_PUBLIC | ACC_FINAL | ACC_STATIC);

  private def visitMainMethod(name: String, des: String): MethodRun =
    new MethodRun(cw.visitMethod(ACC_PUBLIC, name, des, null, null), name)

  private def visitMethod(name: String, des: String): MethodRun =
    new MethodRun(cw.visitMethod(ACC_PUBLIC + ACC_STATIC, name, des, null, null), name)

  {
    val mv = cw.visitMethod(0, "<init>", "()V", null, null)
    mv.visitCode()
    mv.visitVarInsn(ALOAD, 0)
    mv.visitMethodInsn(INVOKESPECIAL, "java/lang/Object", "<init>", "()V", false)
    mv.visitInsn(RETURN)
    mv.visitMaxs(0, 0)
    mv.visitEnd()
  }

  // println("root: " + root)


  private val deps = root.dependencies(0).toSeq

  def visit(): (String, ClassWriter, Seq[Dependency]) = (rootClzName, cw, deps)



  {
    val mv = visitMainMethod("value", "([Ljava/lang/Object;)Lmlang/compiler/semantic/Value;")
    mv.visitCode()
    // println("root deps: " + " --- "  + deps)
    // frame 0: this 1: args, 
    for (i <- 0 until deps.size) {
      mv.visitVarInsn(ALOAD, 1) // args
      mv.emit(i)
      mv.visitInsn(AALOAD)
      val pos = i + 2
      mv.visitVarInsn(ASTORE, pos)
      mv.lookup.put(deps(i), pos)
    }
    mv.emit(root)
    mv.visitInsn(ARETURN)
    mv.visitMaxs(0, 0)
    mv.visitEnd()
  }

  inline def (mv: MethodRun) emit(l: Int): Unit = {
    if (l == 0) mv.visitInsn(ICONST_0)
    else if (l == 1) mv.visitInsn(ICONST_1)
    else if (l == 2) mv.visitInsn(ICONST_2)
    else if (l == 3) mv.visitInsn(ICONST_3)
    else if (l == 4) mv.visitInsn(ICONST_4)
    else if (l == 5) mv.visitInsn(ICONST_5)
    else mv.visitLdcInsn(l)
  }

  inline def (mv: MethodRun) emit(b: Boolean): Unit = {
    mv.visitInsn(if (b) ICONST_1 else ICONST_0)
  }

  // create a value
  inline def (mv: MethodRun) create (name: String, method: String = "apply"): Unit = {
    val ds = ByteCodeGeneratorRun.descriptors
    val clzName = "mlang/compiler/semantic/Value$" + name
    val clzName0 = "mlang.compiler.semantic.Value$" + name
    val desc = ds.get(name + method) match {
      case Some(a) => a
      case None =>
        val mtd = java.lang.Class.forName(clzName0).getMethods.find(_.getName == method).get
        val a = JavaRuntime.getMethodDescriptor(mtd)
        ds.put(name, a)
        a
    }
    if (!visitedInnerClasses.contains(name)) {
      cw.visitInnerClass(clzName, "mlang/compiler/semantic/Value", name, ACC_PUBLIC | ACC_STATIC)
      visitedInnerClasses.add(name)
    }
    mv.visitMethodInsn(INVOKESTATIC, clzName, method, desc, false)
  }


  private def (mv: MethodRun) createLet(
    closure: Abstract.Let
  ): Unit = {
    // load captured local variables to stack
    // create the "function object"
    val captured = closure.dependencies(0).toSeq
    // println(s"$closure with captured $captured")
    val name = s"let${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val mthDesp = s"(${capturedDes})Lmlang/compiler/semantic/Value;"
    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)
    // arguments
    mn.visitCode()
    mn.declareMetas(closure.metas, captured.size)
    mn.emitLocalReferences(closure.definitions, captured.size + closure.metas.size)
    mn.fillMetas(closure.metas, captured.size)
    mn.emit(closure.in)
    mn.visitInsn(ARETURN)
    mn.visitMaxs(0, 0)
    mn.visitEnd()

    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Lscala/Function0;", 
      closureBootstrapHandle,
      closureBootstrapArgs0(0),
      new Handle(
        Opcodes.H_INVOKESTATIC,
        rootClzName,
        name,
        mthDesp,
        false
      ),
      Type.getType(s"()Lmlang/compiler/semantic/Value;")
    )
    mv.visitMethodInsn(INVOKEINTERFACE, "scala/Function0", "apply", "()Ljava/lang/Object;", true)
    mv.visitTypeInsn(CHECKCAST, "mlang/compiler/semantic/Value")
  }


  private def (mn: MethodRun) emitLocalReferences(locals: Seq[Abstract], frontSize: Int): Unit = {
    // create metas in local variables
    for (i <- 0 until locals.size) {
      mn.create("LocalReference", "uninitalized")
      mn.visitVarInsn(ASTORE, frontSize + i)
      mn.lookup.put(Dependency(0, i, 0, DependencyType.Value), frontSize + i)
    }
    for ((m, i) <- locals.zipWithIndex) {
      mn.visitVarInsn(ALOAD, frontSize + i)
      mn.emit(m)
      mn.visitMethodInsn(INVOKEVIRTUAL, "mlang/compiler/semantic/Value$LocalReference", "initialize", localReferenceInitilizeSig)
    }
  }


  private def (mn: MethodRun) declareMetas(metas: Seq[Abstract], frontSize: Int, base: Int = 0): Unit = {
    for (i <- 0 until metas.size) {
      mn.create("Meta", "uninitalized")
      mn.visitVarInsn(ASTORE, frontSize + i)
      mn.lookup.put(Dependency(0, base + i, 0, DependencyType.Meta), frontSize + i)
    }
  }
  
  private def (mn: MethodRun) fillMetas(metas: Seq[Abstract], frontSize: Int): Unit = {
    for ((m, i) <- metas.zipWithIndex) {
      mn.visitVarInsn(ALOAD, frontSize + i)
      mn.emit(m)
      mn.visitMethodInsn(INVOKEVIRTUAL, "mlang/compiler/semantic/Value$Meta", "initialize", metaInitilizeSig)
    }
  }

  private def (mn: MethodRun) emitMetas(metas: Seq[Abstract], frontSize: Int, base: Int = 0): Unit = {
    mn.declareMetas(metas, frontSize, base)
    mn.fillMetas(metas, frontSize)
  }

  private def (mn: MethodRun) emitClosureBody(closure: dbi.Closure, frontSize: Int): Unit = {
    mn.visitCode()
    mn.emitMetas(closure.metas, frontSize)
    mn.emit(closure.term)
    mn.visitInsn(ARETURN)
    mn.visitMaxs(0, 0)
    mn.visitEnd()
  }


  /**
  how do we translate a closure to invoke dynamic?
  first, given the closure, we need to find out all the captured variables, 
  and they are all in current frame!
  */
  private def (mv: MethodRun) createClosure(
    closure: dbi.Closure
  ): Unit = {
    // load captured local variables to stack
    // create the "function object"
    val captured = closure.dependencies(0).toSeq
    // println(s"$closure with captured $captured")
    val argsSize = 1
    val name = s"closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = "Lmlang/compiler/semantic/Value;"
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lmlang/compiler/semantic/Value;"
    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)
    // arguments
    mn.lookup.put(Dependency(0, -1, 0, DependencyType.Value), captured.size)
    mn.emitClosureBody(closure, captured.size + argsSize)
    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Lscala/Function1;", 
      closureBootstrapHandle,
      closureBootstrapArgs0(1),
      new Handle(
        Opcodes.H_INVOKESTATIC,
        rootClzName,
        name,
        mthDesp,
        false
      ),
      Type.getType(s"($selfDesCompressed)Lmlang/compiler/semantic/Value;")
    )
  }



  private def (mv: MethodRun) createAbsClosure(
    closure: dbi.Closure
  ): Unit = {
    // load captured local variables to stack
    // create the "function object"
    val captured = closure.dependencies(0).toSeq
    // println(s"$closure with captured $captured")
    val argsSize = 1
    val name = s"abs_closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = "Lmlang/compiler/semantic/Formula;"
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lmlang/compiler/semantic/Value;"
    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)
    // arguments
    mn.lookup.put(Dependency(0, -1, 0, DependencyType.Formula), captured.size)
    // println(mn.name + mn.lookup)
    mn.emitClosureBody(closure, captured.size + argsSize)
    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Lscala/Function1;", 
      closureBootstrapHandle,
      closureBootstrapArgs0(1),
      new Handle(
        Opcodes.H_INVOKESTATIC,
        rootClzName,
        name,
        mthDesp,
        false
      ),
      Type.getType(s"($selfDesCompressed)Lmlang/compiler/semantic/Value;")
    )
  }

  private def (mv: MethodRun) createValueClosure(
    closure: dbi.Closure
  ): Unit = {
    // load captured local variables to stack
    // create the "function object"
    val captured = closure.dependencies(0).toSeq
    // println(s"$closure with captured $captured")
    val argsSize = 0
    val name = s"value_closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = ""
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lmlang/compiler/semantic/Value;"
    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)

    mn.emitClosureBody(closure, captured.size + argsSize)
    // println(name + " mn " + mn.lookup)
    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Lscala/Function0;", 
      closureBootstrapHandle,
      closureBootstrapArgs0(0),
      new Handle(
        Opcodes.H_INVOKESTATIC,
        rootClzName,
        name,
        mthDesp,
        false
      ),
      Type.getType(s"($selfDesCompressed)Lmlang/compiler/semantic/Value;")
    )
  }




  private def (mv: MethodRun) createMultiClosure(size: (Int, Int), closure: dbi.Closure): Unit = {
    // load captured local variables to stack
    // create the "function object"
    val captured = closure.dependencies(0).toSeq
    // println(s"$closure with captured $captured")
    val argsSize = 2
    val name = s"multi_closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = "Lscala/collection/immutable/Seq;Lscala/collection/immutable/Seq;"
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lmlang/compiler/semantic/Value;"

    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)

    
    mn.visitCode()
    // process arguments -- flatten values from the array to local variables
    mn.visitVarInsn(ALOAD, captured.size + 1) // formula seq
    mn.visitVarInsn(ALOAD, captured.size) // value seq
    for (i <- 0 until size._1) {
      mn.visitInsn(DUP)
      mn.emit(i)
      mn.visitMethodInsn(INVOKEINTERFACE, "scala/collection/SeqOps", "apply", "(I)Ljava/lang/Object;", true);
      mn.visitTypeInsn(CHECKCAST, "mlang/compiler/semantic/Value");
      val pos = captured.size + i
      mn.visitVarInsn(ASTORE, pos)
      mn.lookup.put(Dependency(0, i, 0, DependencyType.Value), pos)
    }
    mn.visitInsn(POP)
    for (i <- 0 until size._2) {
      mn.visitInsn(DUP)
      mn.emit(i)
      mn.visitMethodInsn(INVOKEINTERFACE, "scala/collection/SeqOps", "apply", "(I)Ljava/lang/Object;", true);
      mn.visitTypeInsn(CHECKCAST, "mlang/compiler/semantic/Formula");
      val pos = captured.size + i + size._1
      mn.visitVarInsn(ASTORE, pos)
      mn.lookup.put(Dependency(0, i, 0, DependencyType.Formula), pos)
    }
    mn.visitInsn(POP)

    // put metas after the argments
    mn.emitMetas(closure.metas, captured.size + size._1 + size._2)
    mn.emit(closure.term)
    mn.visitInsn(ARETURN)
    mn.visitMaxs(0, 0)
    mn.visitEnd()

    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Lscala/Function2;", 
      closureBootstrapHandle,
      closureBootstrapArgs0(2),
      new Handle(
        Opcodes.H_INVOKESTATIC,
        rootClzName,
        name,
        mthDesp,
        false
      ),
      Type.getType(s"($selfDesCompressed)Lmlang/compiler/semantic/Value;")
    )
  }
 
  private def (mv: MethodRun) createClosureGraphAgumentsClosure(size: (Int, Int), closure: dbi.Closure): Unit = {
    // load captured local variables to stack
    // create the "function object"
    val captured = closure.dependencies(0).toSeq
    // println(s"$closure with captured $captured")
    val argsSize = 2
    val name = s"multi_closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = "Lscala/collection/immutable/Seq;Lscala/collection/immutable/Seq;"
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lscala/Tuple2;"

    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)

    mn.visitCode()
    // arguments
    mn.visitVarInsn(ALOAD, captured.size + 1) // metas seq
    mn.visitVarInsn(ALOAD, captured.size) // value seq
    for (i <- 0 until size._1) {
      mn.visitInsn(DUP)
      mn.emit(i)
      mn.visitMethodInsn(INVOKEINTERFACE, "scala/collection/SeqOps", "apply", "(I)Ljava/lang/Object;", true);
      mn.visitTypeInsn(CHECKCAST, "mlang/compiler/semantic/Value");
      val pos = captured.size + i
      mn.visitVarInsn(ASTORE, pos)
      mn.lookup.put(Dependency(0, i, 0, DependencyType.Value), pos)
    }
    mn.visitInsn(POP)
    for (i <- 0 until size._2) {
      mn.visitInsn(DUP)
      mn.emit(i)
      mn.visitMethodInsn(INVOKEINTERFACE, "scala/collection/SeqOps", "apply", "(I)Ljava/lang/Object;", true);
      mn.visitTypeInsn(CHECKCAST, "mlang/compiler/semantic/Value");
      val pos = captured.size + i + size._1
      mn.visitVarInsn(ASTORE, pos)
      mn.lookup.put(Dependency(0, i, 0, DependencyType.Meta), pos)
    }
    mn.visitInsn(POP)

    // these is used inside, but also is our result, they are put into local variables first
    mn.emitMetas(closure.metas, captured.size + size._1 + size._2, size._2)
    // create a new seq of newly emited metas
    mn.createSeq(closure.metas.indices, "mlang/compiler/semantic/Value", i => mn.visitVarInsn(ALOAD, captured.size + size._1 + size._2 + i))
    mn.emit(closure.term)

    // tuple them up
    mn.visitMethodInsn(INVOKESTATIC, "scala/Tuple2", "apply", "(Ljava/lang/Object;Ljava/lang/Object;)Lscala/Tuple2;", false);

    mn.visitInsn(ARETURN)
    mn.visitMaxs(0, 0)
    mn.visitEnd()

    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Lscala/Function2;", 
      closureBootstrapHandle,
      closureBootstrapArgs0(2),
      new Handle(
        Opcodes.H_INVOKESTATIC,
        rootClzName,
        name,
        mthDesp,
        false
      ),
      Type.getType(s"($selfDesCompressed)Lscala/Tuple2;")
    )
  }

  
  private def (mv: MethodRun) createClosureGraphRestrictionsClosure(dsize: Int, vsize: Int, msize: Int, system: dbi.System): Unit = {
    /* for example set_trunc:
    Lambda(Closure(List(),
    Sum(Some(Inductively(5,Function(Universe(0),false,Closure(List(),Universe(0))),Vector(Reference(0,-1)))),true,List(
      Constructor(in,ClosureGraph(List(Node(false,empty Range 0 until 0,Closure(List(),Reference(1,-1)))),0,Map())),
      Constructor(squash,ClosureGraph(List(
        Node(false,empty Range 0 until 0,Closure(List(),App(Reference(2,152),Reference(1,-1)))),
        Node(false,Range 0 until 1,Closure(List(),App(Reference(2,152),Reference(1,-1))))
        Node(false,Range 0 until 2,Closure(List(),PathType(Closure(List(),App(Reference(3,152),Reference(2,-1))),Reference(0,0),Reference(0,1)))),
        Node(false,Range 0 until 3,Closure(List(),PathType(Closure(List(),App(Reference(3,152),Reference(2,-1))),Reference(0,0),Reference(0,1))))),2,
          Map(Neg(Reference(0,0)) -> Closure(List(),PathApp(Reference(1,2),Reference(1,1))), Reference(0,0) -> Closure(List(),PathApp(Reference(1,3),Reference(1,1))), Neg(Reference(0,1)) -> Closure(List(),Reference(1,0)), Reference(0,1) -> Closure(List(),Reference(1,1)))))))))
    */
    val captured = dbi.ClosureGraphRestrictionSystemDbi.dependencies(system, 1)
    /// println("first " + captured)
    val argsSize = 1
    val name = s"closure_graph_ris${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = "Lscala/collection/immutable/Seq;"
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lscala/collection/immutable/Map;"

    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c, i)

    mn.visitCode()
    // arguments
    mn.visitVarInsn(ALOAD, captured.size) // formula seq
    for (i <- 0 until dsize) {
      mn.visitInsn(DUP)
      mn.emit(i)
      mn.visitMethodInsn(INVOKEINTERFACE, "scala/collection/SeqOps", "apply", "(I)Ljava/lang/Object;", true);
      mn.visitTypeInsn(CHECKCAST, "mlang/compiler/semantic/Formula");
      val pos = captured.size + i
      mn.visitVarInsn(ASTORE, pos)
      mn.lookup.put(Dependency(0, i, 0, DependencyType.Formula), pos)
    }
    mn.visitInsn(POP)

    mn.createSystem(system, c => {
      // here is 1, because it doesn't include closure graph parameter and dimensions
      val innerCaptured = c.dependencies(1).toSeq
      // println("inner captured " + innerCaptured)

      val innerCapturedDes = innerCaptured.map(_.typ.descriptor).mkString
      val dimensionsCaptured = (0 until dsize).map(_ => "Lmlang/compiler/semantic/Formula;").mkString
      val innerSelfDesCompressed = "Lscala/collection/immutable/Seq;Lscala/collection/immutable/Seq;"
      val innerMthDesp = s"(${innerCapturedDes}${dimensionsCaptured}$innerSelfDesCompressed)Lmlang/compiler/semantic/Value;"
      val innerName = s"clsoure_graph_inner_${mtdgen()}"
      val mm = visitMethod(innerName, innerMthDesp)
      for ((cc, ii) <- innerCaptured.zipWithIndex) mm.lookup.put(cc.diff(2), ii)
      for (i <- 0 until dsize) mm.lookup.put(Dependency(1, i, 0, DependencyType.Formula), innerCaptured.size + i)
      mm.visitCode()
      val capturedTotalSize = innerCaptured.size + dsize
      // process arguments -- flatten values from the array to local variables
      mm.visitVarInsn(ALOAD, capturedTotalSize + 1) // meta seq
      mm.visitVarInsn(ALOAD, capturedTotalSize) // value seq
      for (i <- 0 until vsize) {
        mm.visitInsn(DUP)
        mm.emit(i)
        mm.visitMethodInsn(INVOKEINTERFACE, "scala/collection/SeqOps", "apply", "(I)Ljava/lang/Object;", true);
        mm.visitTypeInsn(CHECKCAST, "mlang/compiler/semantic/Value");
        val pos = capturedTotalSize + i
        mm.visitVarInsn(ASTORE, pos)
        mm.lookup.put(Dependency(1, i, 0, DependencyType.Value), pos)
      }
      mm.visitInsn(POP)
      for (i <- 0 until msize) {
        mm.visitInsn(DUP)
        mm.emit(i)
        mm.visitMethodInsn(INVOKEINTERFACE, "scala/collection/SeqOps", "apply", "(I)Ljava/lang/Object;", true);
        mm.visitTypeInsn(CHECKCAST, "mlang/compiler/semantic/Value");
        val pos = capturedTotalSize + i + vsize
        mm.visitVarInsn(ASTORE, pos)
        mm.lookup.put(Dependency(1, i, 0, DependencyType.Meta), pos)
      }
      mm.visitInsn(POP)

      mm.emitMetas(c.metas, innerCaptured.size + dsize + msize + vsize) // current layer's meta
      mm.emit(c.term)
      mm.visitInsn(ARETURN)
      mm.visitMaxs(0, 0)
      mm.visitEnd()

      for (c <- innerCaptured) mn.visitVarInsn(ALOAD, mn.lookup(c))
      for (i <- 0 until dsize) mn.visitVarInsn(ALOAD, mn.lookup(Dependency(0, i, 0, DependencyType.Formula)))
      val p = s"($innerSelfDesCompressed)Lmlang/compiler/semantic/Value;"
      //println(p)
      mn.visitInvokeDynamic(
        "apply", 
        s"(${innerCapturedDes}${dimensionsCaptured})Lscala/Function2;", 
        closureBootstrapHandle,
        closureBootstrapArgs0(2),
        new Handle(
          Opcodes.H_INVOKESTATIC,
          rootClzName,
          innerName,
          innerMthDesp,
          false
        ),
        Type.getType(s"($innerSelfDesCompressed)Lmlang/compiler/semantic/Value;")
      )
    })

    mn.visitInsn(ARETURN)
    mn.visitMaxs(0, 0)
    mn.visitEnd()

    // println(system)
    // println(captured)
    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Lscala/Function1;", 
      closureBootstrapHandle,
      closureBootstrapArgs0(1),
      new Handle(
        Opcodes.H_INVOKESTATIC,
        rootClzName,
        name,
        mthDesp,
        false
      ),
      Type.getType(s"($selfDesCompressed)Lscala/collection/immutable/Map;")
    )
  }

  private def (mv: MethodRun) createClosureGraph(graph: dbi.ClosureGraph): Unit = {
    mv.visitFieldInsn(GETSTATIC, "mlang/compiler/semantic/ClosureGraph$", "MODULE$", "Lmlang/compiler/semantic/ClosureGraph$;");
    var i = 0
    var ms = 0
    mv.createSeq(graph.nodes, "mlang/compiler/semantic/ClosureGraphArguments", node => {
      mv.createIntSeq(node.deps)
      mv.emit(node.typ.metas.size)
      // we give the arguments as the values/metas before current node
      mv.createClosureGraphAgumentsClosure((i, ms), node.typ)
      i += 1
      ms += node.typ.metas.size
      mv.visitMethodInsn(INVOKESTATIC, "mlang/compiler/semantic/ClosureGraphArguments", "apply", "(Lscala/collection/immutable/Seq;ILscala/Function2;)Lmlang/compiler/semantic/ClosureGraphArguments;", false)
    })
    mv.emit(graph.dims)
    if (graph.dims == 0) mv.visitInsn(ACONST_NULL)
    else mv.createClosureGraphRestrictionsClosure(graph.dims, i, ms, graph.restrictions)
    mv.visitMethodInsn(INVOKEVIRTUAL, "mlang/compiler/semantic/ClosureGraph$", "apply", "(Lscala/collection/immutable/Seq;ILscala/Function1;)Lmlang/compiler/semantic/ClosureGraph;", false);
  }


  inline private def (mv: MethodRun) createSystem(system: dbi.System, bd: dbi.Closure => Unit): Unit = {
    mv.visitFieldInsn(GETSTATIC, "scala/Predef$", "MODULE$", "Lscala/Predef$;");
    mv.visitMethodInsn(INVOKEVIRTUAL, "scala/Predef$", "Map", "()Lscala/collection/immutable/Map$;", false);
    mv.createSeq(system.toSeq, "scala/Tuple2", pair => {
      mv.emit(pair._1)
      bd(pair._2)
      mv.visitMethodInsn(INVOKESTATIC, "scala/Tuple2", "apply", "(Ljava/lang/Object;Ljava/lang/Object;)Lscala/Tuple2;", false);
    })
    mv.visitMethodInsn(INVOKEINTERFACE, "scala/collection/MapFactory", "apply", "(Lscala/collection/immutable/Seq;)Ljava/lang/Object;", true);
    mv.visitTypeInsn(CHECKCAST, "scala/collection/immutable/Map");
  }
  
  private def (mv: MethodRun) createValueSystem(system: dbi.System): Unit = {
    mv.createSystem(system, a => mv.diff(1).createValueClosure(a))
  }

  private def (mv: MethodRun) createAbsSystem(system: dbi.System): Unit = {
    mv.createSystem(system, a => mv.diff(1).createAbsClosure(a))
  }

  private def (mv: MethodRun) emit(term: dbi.Formula): Unit = {
    term match {
      case dbi.Formula.Reference(up, index) =>
        // println(mv.name + " " + mv.lookup)
        mv.visitVarInsn(ALOAD, mv.lookup(Dependency(up, index, 0, DependencyType.Formula)))
      case dbi.Formula.True =>
        mv.visitFieldInsn(GETSTATIC, "mlang/compiler/semantic/Formula$True$", "MODULE$", "Lmlang/compiler/semantic/Formula$True$;")
      case dbi.Formula.False =>
        mv.visitFieldInsn(GETSTATIC, "mlang/compiler/semantic/Formula$False$", "MODULE$", "Lmlang/compiler/semantic/Formula$False$;")
      case dbi.Formula.And(l, r) =>
        mv.visitFieldInsn(GETSTATIC, "mlang/compiler/semantic/Formula$And$", "MODULE$", "Lmlang/compiler/semantic/Formula$And$;");
        mv.emit(l)
        mv.emit(r)
        mv.visitMethodInsn(INVOKEVIRTUAL, "mlang/compiler/semantic/Formula$And$", "apply", "(Lmlang/compiler/semantic/Formula;Lmlang/compiler/semantic/Formula;)Lmlang/compiler/semantic/Formula$And;", false);
      case dbi.Formula.Or(l, r) =>
        mv.visitFieldInsn(GETSTATIC, "mlang/compiler/semantic/Formula$Or$", "MODULE$", "Lmlang/compiler/semantic/Formula$Or$;");
        mv.emit(l)
        mv.emit(r)
        mv.visitMethodInsn(INVOKEVIRTUAL, "mlang/compiler/semantic/Formula$Or$", "apply", "(Lmlang/compiler/semantic/Formula;Lmlang/compiler/semantic/Formula;)Lmlang/compiler/semantic/Formula$Or;", false);
      case dbi.Formula.Neg(l) =>
        mv.visitFieldInsn(GETSTATIC, "mlang/compiler/semantic/Formula$Neg$", "MODULE$", "Lmlang/compiler/semantic/Formula$Neg$;");
        mv.emit(l)
        mv.visitMethodInsn(INVOKEVIRTUAL, "mlang/compiler/semantic/Formula$Neg$", "apply", "(Lmlang/compiler/semantic/Formula;)Lmlang/compiler/semantic/Formula$Neg;", false);
    } 
  }

  private def [T] (mv: MethodRun) createOption(v: Option[T], emit: T => Unit): Unit = {
    v match {
      case None =>
        mv.visitFieldInsn(GETSTATIC, "scala/None$", "MODULE$", "Lscala/None$;")
      case Some(j) =>
        mv.visitFieldInsn(GETSTATIC, "scala/Option$", "MODULE$", "Lscala/Option$;")
        emit(j)
        mv.visitMethodInsn(INVOKEVIRTUAL, "scala/Option$", "apply", "(Ljava/lang/Object;)Lscala/Option;", false);
    }
  }

  inline private def (mv: MethodRun) createIntSeq(vs: Seq[Int]): Unit = {
    if (vs.size == 0) {
      mv.visitFieldInsn(GETSTATIC, "scala/collection/immutable/ArraySeq$", "MODULE$", "Lscala/collection/immutable/ArraySeq$;")
      mv.visitFieldInsn(GETSTATIC, "scala/reflect/ClassTag$", "MODULE$", "Lscala/reflect/ClassTag$;")
      mv.visitFieldInsn(GETSTATIC, "java/lang/Integer", "TYPE", "Ljava/lang/Class;")
      mv.visitMethodInsn(INVOKEVIRTUAL, "scala/reflect/ClassTag$", "apply", "(Ljava/lang/Class;)Lscala/reflect/ClassTag;", false)
      mv.visitMethodInsn(INVOKEVIRTUAL, "scala/collection/immutable/ArraySeq$", "empty", "(Lscala/reflect/ClassTag;)Lscala/collection/immutable/ArraySeq;", false)
    } else {
      mv.visitTypeInsn(NEW, "scala/collection/immutable/ArraySeq$ofInt");
      mv.visitInsn(DUP);
      mv.emit(vs.size)
      mv.visitIntInsn(NEWARRAY, T_INT);
      for (i <- 0 until vs.size) {
        mv.visitInsn(DUP)
        mv.emit(i)
        mv.emit(vs(i))
        mv.visitInsn(IASTORE)
      }
      mv.visitTypeInsn(CHECKCAST, "[I");
      mv.visitMethodInsn(INVOKESPECIAL, "scala/collection/immutable/ArraySeq$ofInt", "<init>", "([I)V", false);
    }
  }

  inline private def [T] (mv: MethodRun) createSeq(vs: Seq[T], typ: String, emit: T => Unit): Unit = {
    if (vs.size == 0) {
      mv.visitFieldInsn(GETSTATIC, "scala/collection/immutable/ArraySeq$", "MODULE$", "Lscala/collection/immutable/ArraySeq$;");
      mv.visitFieldInsn(GETSTATIC, "scala/reflect/ClassTag$", "MODULE$", "Lscala/reflect/ClassTag$;");
      mv.visitLdcInsn(Type.getType(s"L$typ;"));
      mv.visitMethodInsn(INVOKEVIRTUAL, "scala/reflect/ClassTag$", "apply", "(Ljava/lang/Class;)Lscala/reflect/ClassTag;", false);
      mv.visitMethodInsn(INVOKEVIRTUAL, "scala/collection/immutable/ArraySeq$", "empty", "(Lscala/reflect/ClassTag;)Lscala/collection/immutable/ArraySeq;", false);
    } else {
      mv.visitTypeInsn(NEW, "scala/collection/immutable/ArraySeq$ofRef")
      mv.visitInsn(DUP)
      mv.emit(vs.size)
      mv.visitTypeInsn(ANEWARRAY, typ)
      for (i <- 0 until vs.size) {
        mv.visitInsn(DUP)
        mv.emit(i)
        emit(vs(i))
        mv.visitInsn(AASTORE)
      }
      mv.visitTypeInsn(CHECKCAST, "[Ljava/lang/Object;");
      mv.visitMethodInsn(INVOKESPECIAL, "scala/collection/immutable/ArraySeq$ofRef", "<init>", "([Ljava/lang/Object;)V", false)
    }
  }

  private def (mv: MethodRun) emit(term: dbi.Inductively): Unit = {
    mv.visitLdcInsn(term.id)
    mv.emit(term.typ)
    mv.createSeq(term.ps, "mlang/compiler/semantic/Value", a => mv.emit(a))
    mv.visitMethodInsn(INVOKESTATIC, "mlang/compiler/semantic/Inductively", "apply", "(JLmlang/compiler/semantic/Value;Lscala/collection/immutable/Seq;)Lmlang/compiler/semantic/Inductively;", false)
  }

  private def (mv: MethodRun) emit(term: Abstract): Unit = {
    // println(term)
    // LATER we might be able to macro/typeclass it, but i don't have time, compared to moving away form Scala code generation
    term match {
      case Abstract.Universe(l) =>
        mv.emit(l)
        mv.create("Universe")
      case Abstract.Reference(x, i, lvl) =>
        mv.visitVarInsn(ALOAD, mv.lookup(Dependency(x, i, lvl, DependencyType.Value)))
      case Abstract.MetaReference(x, i, lvl) =>
        mv.visitVarInsn(ALOAD, mv.lookup(Dependency(x, i, lvl, DependencyType.Meta)))
      case l@Abstract.Let(metas, definitions, in) =>
        mv.createLet(l)
      case Abstract.Function(etype, domain, codomain) =>
        val i = tunnel(etype)
        mv.emit(i)
        mv.visitMethodInsn(INVOKESTATIC, "mlang/compiler/ByteCodeGeneratorRun", "getETypeFunction", "(I)Lmlang/compiler/EType$Function;", false);
        mv.emit(domain)
        mv.createClosure(codomain)
        mv.create("Function")
      case Abstract.Lambda(closure) =>
        mv.createClosure(closure)
        mv.create("Lambda")
      case Abstract.App(left, right) =>
        mv.emit(left)
        mv.emit(right)
        mv.create("App")
      case Abstract.Record(etype, id, nodes) =>
        val i = tunnel(etype)
        mv.emit(i)
        mv.visitMethodInsn(INVOKESTATIC, "mlang/compiler/ByteCodeGeneratorRun", "getETypeRecord", "(I)Lmlang/compiler/EType$Record;", false);
        mv.createOption(id, a => mv.emit(a))
        mv.createClosureGraph(nodes)
        mv.create("Record")
      case Abstract.Projection(left, field) =>
        mv.emit(left)
        mv.emit(field)
        mv.create("Projection")
      case Abstract.Sum(etype, id, hit, constructors) =>
        val i = tunnel(etype)
        mv.emit(i)
        mv.visitMethodInsn(INVOKESTATIC, "mlang/compiler/ByteCodeGeneratorRun", "getETypeSum", "(I)Lmlang/compiler/EType$Sum;", false);
        mv.createOption(id, a => mv.emit(a))
        mv.emit(hit)
        mv.createSeq(constructors,  "mlang/compiler/semantic/ClosureGraph", a => {
          mv.createClosureGraph(a)
        })
        mv.create("Sum")
      case Abstract.Make(vs) =>
        mv.createSeq(vs, "mlang/compiler/semantic/Value", a => mv.emit(a))
        mv.create("Make")
      case Abstract.Construct(name, vs, ds, ty) =>
        mv.emit(name)
        mv.createSeq(vs, "mlang/compiler/semantic/Value", a => mv.emit(a))
        if (ds.isEmpty) {
          assert(ty.isEmpty)
          mv.create("SimpleConstruct")
        } else {
          mv.createSeq(ds, "mlang/compiler/semantic/Formula", a => mv.emit(a))
          mv.createValueSystem(ty)
          mv.create("HitConstruct")
        }
      case Abstract.PatternLambda(id, dom, codomain, cases) =>
        mv.visitLdcInsn(id)
        mv.emit(dom)
        mv.createClosure(codomain)
        mv.createSeq(cases, "mlang/compiler/semantic/Case", a => {
          val id = tunnel(a.pattern)
          mv.emit(id);
          mv.visitMethodInsn(INVOKESTATIC, "mlang/compiler/ByteCodeGeneratorRun", "getPattern", "(I)Lmlang/compiler/Pattern;", false)
          mv.createMultiClosure(a.pattern.atomCount, a.body)
          mv.visitMethodInsn(INVOKESTATIC, "mlang/compiler/semantic/Case", "apply", "(Lmlang/compiler/Pattern;Lscala/Function2;)Lmlang/compiler/semantic/Case;", false)
        })
        mv.create("PatternLambda")
      case Abstract.PathApp(left, right) =>
        mv.emit(left)
        mv.emit(right)
        mv.create("PathApp")
      case Abstract.PathType(typ, left, right) =>
        mv.createAbsClosure(typ)
        mv.emit(left)
        mv.emit(right)
        mv.create("PathType")
      case Abstract.PathLambda(body) =>
        mv.createAbsClosure(body)
        mv.create("PathLambda")
      case Abstract.Transp(tp, dir, base) =>
        mv.createAbsClosure(tp)
        mv.emit(dir)
        mv.emit(base)
        mv.create("Transp")
      case Abstract.Hcomp(tp, base, faces) =>
        mv.emit(tp)
        mv.emit(base)
        mv.createAbsSystem(faces)
        mv.create("Hcomp")
      case Abstract.Comp(tp, base, faces) =>
        mv.createAbsClosure(tp)
        mv.emit(base)
        mv.createAbsSystem(faces)
        mv.create("Comp")
      case Abstract.GlueType(tp, faces) =>
        mv.emit(tp)
        mv.createValueSystem(faces)
        mv.create("GlueType")
      case Abstract.Glue(base, faces) =>
        mv.emit(base)
        mv.createValueSystem(faces)
        mv.create("Glue")
      case Abstract.Unglue(ty, base, iu, faces) =>
        mv.emit(ty)
        mv.emit(base)
        mv.emit(iu)
        mv.createValueSystem(faces)
        mv.create("Unglue")
    }
  }

}

trait PlatformEvaluator extends Evaluator {

  protected def platformEval(term: Abstract): Value = Benchmark.HoasCompile {
    val (rootClzName, cw, ds) = Benchmark.HoasBytecodeVisit { new ByteCodeGeneratorRun(term).visit() }
    val bytecode = Benchmark.HoasBytecodeEmit { cw.toByteArray }
    if (false) {
      val f = new java.io.File(rootClzName + ".class")
      val fos = new java.io.FileOutputStream(f)
      fos.write(bytecode)
      fos.close()
      org.objectweb.asm.util.ASMifier.main(Array(f.getPath))
      f.delete()
    }
    val hd = Benchmark.HoasBytecodeCompile {
        val clz = PlatformEvaluatorHelpers.loadClass(rootClzName, bytecode).asInstanceOf[Class[Holder]]
        val ch = clz.getDeclaredConstructors()(0)
        ch.setAccessible(true)
        ch.newInstance(Array[Object](): _*).asInstanceOf[Holder]
    }
    val args = new Array[Object](ds.size)
    for (i <- 0 until ds.size) {
      args(i) = getDependency(ds(i))
    }
    val ret = hd.value(args)
    ret
  }
}
