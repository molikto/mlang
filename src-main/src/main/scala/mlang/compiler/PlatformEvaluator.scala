package mlang.compiler

import mlang.compiler.semantic.given
import mlang.compiler.semantic.Value
import mlang.compiler.dbi.{Abstract, DependencyType, Dependency}
import mlang.compiler.dbi.given
import mlang.utils._
import scala.collection.mutable

trait Holder {
  def value(vs: Array[Object]): Value
}


import org.objectweb.asm._
import Opcodes._

class MethodRun(val mv: MethodVisitor, val name: String = "") extends MethodRunJava {
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

  private val patterns = mutable.ArrayBuffer[Pattern]()
  private def patternTunnel(a: Pattern): Int = {
    patterns.append(a)
    patterns.size - 1
  }

  def getPattern(i: Int): Pattern = {
    patterns(i)
  }

  private val closureBootstrapArgs0 = Seq(
    Type.getType("()Ljava/lang/Object;"),
    Type.getType("(Ljava/lang/Object;)Ljava/lang/Object;"),
    Type.getType("(Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;"),
    Type.getType("(Ljava/lang/Object;Ljava/lang/Object;Ljava/lang/Object;)Ljava/lang/Object;")
  )

  val metaInitilizeSig = mlang.utils.Runtime.getMethodDescriptor(classOf[Value.Meta].getMethods.find(_.getName == "initialize").get)

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
  private val rootClzName = s"mlang_generated${clzgen()}"
  cw.visit(V12, ACC_SUPER, rootClzName, null, "java/lang/Object", Array("mlang/compiler/Holder"))
  cw.visitInnerClass("java/lang/invoke/MethodHandles$Lookup", "java/lang/invoke/MethodHandles", "Lookup", ACC_PUBLIC | ACC_FINAL | ACC_STATIC)
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


  private val deps = root.dependencies(0).toSeq

  def emit(): (Holder, Seq[Dependency]) = {
    val bc = cw.toByteArray
    if (false) {
      val fos = new java.io.FileOutputStream(new java.io.File(rootClzName + ".class"))
      fos.write(bc)
      fos.close()
    }
    val clz = MethodRunJava.loadClass(rootClzName, bc).asInstanceOf[Class[Holder]]
    val ch = clz.getDeclaredConstructors()(0)
    ch.setAccessible(true)
    val hd = ch.newInstance(Array[Object](): _*).asInstanceOf[Holder]
    (hd, deps)
  }

  {
    val mv = visitMainMethod("value", "([Ljava/lang/Object;)Lmlang/compiler/semantic/Value;")
    mv.visitCode()
    // println("root deps: " + root + " --- "  + deps)
    // frame 0: this, 1: args
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
        val a = mlang.utils.Runtime.getMethodDescriptor(mtd)
        ds.put(name, a)
        a
    }
    if (!visitedInnerClasses.contains(name)) {
      cw.visitInnerClass(clzName, "mlang/compiler/semantic/Value", name, ACC_PUBLIC | ACC_STATIC)
      visitedInnerClasses.add(name)
    }
    mv.visitMethodInsn(INVOKESTATIC, clzName, method, desc, false)
  }


  // create a value
  inline def (mv: MethodRun) metaInitalize (): Unit = {
    mv.visitMethodInsn(INVOKEVIRTUAL, "mlang/compiler/semantic/Value$Meta", "initialize", metaInitilizeSig)
  }


  private def (mn: MethodRun) emitMetas(metas: Seq[Abstract], frontSize: Int): Unit = {
    // create metas in local variables
    for (i <- 0 until metas.size) {
      mn.create("Meta", "uninitalized")
      mn.visitVarInsn(ASTORE, frontSize + i)
      mn.lookup.put(Dependency(0, i, DependencyType.Meta), frontSize + i)
    }
    for ((m, i) <- metas.zipWithIndex) {
      mn.visitVarInsn(ALOAD, frontSize + i)
      mn.emit(m)
      mn.metaInitalize()
    }
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
    val frontSize = captured.size + argsSize
    val name = s"closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = "Lmlang/compiler/semantic/Value;"
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lmlang/compiler/semantic/Value;"
    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)
    // arguments
    mn.lookup.put(Dependency(0, -1, DependencyType.Value), captured.size)
    mn.emitClosureBody(closure, frontSize)
    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Ldotty/runtime/function/JFunction1;", 
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
    val frontSize = captured.size + argsSize
    val name = s"closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = "Lmlang/compiler/semantic/Formula;"
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lmlang/compiler/semantic/Value;"
    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)
    // arguments
    mn.lookup.put(Dependency(0, -1, DependencyType.Formula), captured.size)
    // println(mn.name + mn.lookup)
    mn.emitClosureBody(closure, frontSize)
    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Ldotty/runtime/function/JFunction1;", 
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
    val frontSize = captured.size + argsSize
    val name = s"closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = ""
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lmlang/compiler/semantic/Value;"
    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)
    mn.emitClosureBody(closure, frontSize)
    // println(name + " mn " + mn.lookup)
    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Ldotty/runtime/function/JFunction0;", 
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


  private def (mv: MethodRun) createMultiClosure(closure: dbi.Closure): Unit = {
    // load captured local variables to stack
    // create the "function object"
    val captured = closure.dependencies(0).toSeq
    // println(s"$closure with captured $captured")
    val argsSize = 2
    val frontSize = captured.size + argsSize
    val name = s"closure${mtdgen()}"
    val capturedDes = captured.map(_.typ.descriptor).mkString
    val selfDesCompressed = "Lmlang/compiler/semantic/Formula;"
    val mthDesp = s"(${capturedDes}$selfDesCompressed)Lmlang/compiler/semantic/Value;"
    val mn = visitMethod(name, mthDesp)
    // captured
    for ((c, i) <- captured.zipWithIndex) mn.lookup.put(c.diff(1), i)
    // arguments
    mn.lookup.put(Dependency(0, -1, DependencyType.Formula), captured.size)
    mn.emitClosureBody(closure, frontSize)
    for (c <- captured) mv.visitVarInsn(ALOAD, mv.lookup(c))
    mv.visitInvokeDynamic(
      "apply", 
      s"($capturedDes)Ldotty/runtime/function/JFunction1;", 
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


  inline private def (mv: MethodRun) createSystem(system: dbi.System, bd: dbi.Closure => Unit): Unit = {
    mv.visitFieldInsn(GETSTATIC, "scala/Predef$", "MODULE$", "Lscala/Predef$;");
    mv.visitMethodInsn(INVOKEVIRTUAL, "scala/Predef$", "Map", "()Lscala/collection/immutable/Map$;", false);
    mv.createSeq(system.toSeq, "scala/Tuple2", pair => {
      mv.visitFieldInsn(GETSTATIC, "scala/Tuple2$", "MODULE$", "Lscala/Tuple2$;");
      mv.emit(pair._1)
      bd(pair._2)
      mv.visitMethodInsn(INVOKEVIRTUAL, "scala/Tuple2$", "apply", "(Ljava/lang/Object;Ljava/lang/Object;)Lscala/Tuple2;", false);
    })
    mv.visitMethodInsn(INVOKEINTERFACE, "scala/collection/MapFactory", "apply", "(Lscala/collection/immutable/Seq;)Ljava/lang/Object;", true);
    mv.visitTypeInsn(CHECKCAST, "scala/collection/immutable/Map");
  }
  
  private def (mv: MethodRun) createValueSystem(system: dbi.System): Unit = {
    mv.createSystem(system, a => mv.diff(1).createValueClosure(a))
  }

  private def (mv: MethodRun) createClosureSystem(system: dbi.System): Unit = {
    mv.createSystem(system, a => mv.diff(1).createClosure(a))
  }

  private def (mv: MethodRun) createAbsSystem(system: dbi.System): Unit = {
    mv.createSystem(system, a => mv.diff(1).createAbsClosure(a))
  }

  private def (mv: MethodRun) createMultiClosureSystem(system: dbi.System): Unit = {
    mv.createSystem(system, a => mv.diff(1).createMultiClosure(a))
  }

  private def (mv: MethodRun) emit(term: dbi.Formula): Unit = {
    term match {
      case dbi.Formula.Reference(up, index) =>
        // println(mv.name + " " + mv.lookup)
        mv.visitVarInsn(ALOAD, mv.lookup(Dependency(up, index, DependencyType.Formula)))
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

  private def (mv: MethodRun) createSeq[T](vs: Seq[T], typ: String, emit: T => Unit): Unit = {
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

  private def (mv: MethodRun) emit(term: Abstract): Unit = {
    // println(term)
    // LATER we might be able to macro/typeclass it, but i don't have time, compared to moving away form Scala code generation
    term match {
      case Abstract.Universe(l) =>
        mv.emit(l)
        mv.create("Universe")
      case Abstract.Reference(x, i) =>
        mv.visitVarInsn(ALOAD, mv.lookup(Dependency(x, i, DependencyType.Value)))
      case Abstract.MetaReference(x, i) =>
        mv.visitVarInsn(ALOAD, mv.lookup(Dependency(x, i, DependencyType.Meta)))
      case Abstract.Let(metas, definitions, in) =>
        ???
      case Abstract.Function(domain, impl, codomain) =>
        mv.emit(domain)
        mv.emit(impl)
        mv.createClosure(codomain)
        mv.create("Function")
      case Abstract.Lambda(closure) =>
        mv.createClosure(closure)
        mv.create("Lambda")
      case Abstract.App(left, right) =>
        mv.emit(left)
        mv.emit(right)
        mv.create("App")
      case Abstract.Record(id, names, nodes) =>
        ???
      case Abstract.Projection(left, field) =>
        mv.emit(left)
        mv.emit(field)
        mv.create("Projection")
      case Abstract.Sum(id, hit, constructors) =>
        ???
      case Abstract.Make(vs) =>
        mv.createSeq(vs, "mlang/compiler/semantic/Value", a => mv.emit(a))
        mv.create("Make")
      case Abstract.Construct(name, vs, ds, ty) =>
        ???
      case Abstract.PatternLambda(id, dom, codomain, cases) =>
        mv.visitLdcInsn(id)
        mv.emit(dom)
        mv.createClosure(codomain)
        mv.createSeq(cases, "mlang/compiler/semantic/Case", a => {
          val id = patternTunnel(a.pattern)
          mv.emit(id);
          mv.visitMethodInsn(INVOKESTATIC, "mlang/compiler/ByteCodeGeneratorRun", "getPattern", "(I)Lmlang/compiler/Pattern;", false)
          mv.createMultiClosure(a.body)
          mv.visitMethodInsn(INVOKESTATIC, "mlang/compiler/semantic/Case", "apply", "(Lmlang/compiler/Pattern;Lscala/Function2)Lmlang/compiler/semantic/Case;", false)
        })
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

  protected def platformEval(term: Abstract): Value = {
    // val term = Abstract.Make(Seq(Abstract.PathApp(
    //   Abstract.Universe(23),
    //    dbi.Formula.Or(dbi.Formula.Neg(dbi.Formula.True), dbi.Formula.And(dbi.Formula.False, dbi.Formula.True))), Abstract.PathType(dbi.Closure(Seq.empty, Abstract.Universe(0)), Abstract.Universe(0), Abstract.Universe(0))))
    val (hd, ds) = new ByteCodeGeneratorRun(term).emit()
    val args = new Array[Object](ds.size)
    for (i <- 0 until ds.size) {
      args(i) = getDependency(ds(i))
    }
    val ret = hd.value(args)
    ret
  }
}
