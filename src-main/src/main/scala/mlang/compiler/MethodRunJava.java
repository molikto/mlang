package mlang.compiler;

import org.objectweb.asm.*;
import org.objectweb.asm.tree.*;
import org.objectweb.asm.util.*;
import java.io.*;
import java.util.*;



// some hack, because dotty is buggy
public abstract class MethodRunJava {
    public abstract MethodVisitor mv();
    public void visitInvokeDynamic(
        java.lang.String name,
        java.lang.String descriptor,
        Handle bootstrapMethodHandle,
        java.lang.Object obj1,
        java.lang.Object obj2,
        java.lang.Object obj3
    ) {
        mv().visitInvokeDynamicInsn(name, descriptor, bootstrapMethodHandle, new Object[] {obj1, obj2, obj3});
    }

  public static Class<Holder> loadClass(String className, byte[] b) {
    // Override defineClass (as it is protected) and define the class.
    Class clazz = null;
    try {
      ClassLoader loader = MethodRunJava.class.getClassLoader();
      Class cls = Class.forName("java.lang.ClassLoader");
      java.lang.reflect.Method method =
          cls.getDeclaredMethod(
              "defineClass", 
              new Class[] { String.class, byte[].class, int.class, int.class });

      // Protected method invocation.
      method.setAccessible(true);
      try {
        Object[] args = 
            new Object[] { className, b, new Integer(0), new Integer(b.length)};
        clazz = (Class) method.invoke(loader, args);
      } finally {
        method.setAccessible(false);
      }
    } catch (Exception e) {
      e.printStackTrace();
      System.exit(1);
    }
    return clazz;
  }



  public static byte[] getByteCodeOf(Class<?> c) throws IOException {
    //in the following - c.getResourceAsStream will return null..
    try (InputStream input = c.getResourceAsStream('/' + c.getName().replace('.', '/')+ ".class")){
        byte[] result = new byte[input.available()];
        input.read(result);
        return result;
    }
  }

   public static void printByteCode(Class<?> c) throws IOException {
     print(getByteCodeOf(c));
   }

   public static void print(byte[] bytecode) throws IOException {
        ClassReader reader = new ClassReader(bytecode);
        ClassNode classNode = new ClassNode();
        reader.accept(classNode,0);
        @SuppressWarnings("unchecked")
        final List<MethodNode> methods = classNode.methods;
        for(MethodNode m: methods){
             InsnList inList = m.instructions;
             System.out.println(m.name);
             for(int i = 0; i< inList.size(); i++){
                 System.out.print(insnToString(inList.get(i)));
             }
        }
    }

    public static String insnToString(AbstractInsnNode insn){
        insn.accept(mp);
        StringWriter sw = new StringWriter();
        printer.print(new PrintWriter(sw));
        printer.getText().clear();
        return sw.toString();
    }

    private static Printer printer = new Textifier();
    private static TraceMethodVisitor mp = new TraceMethodVisitor(printer); 
}