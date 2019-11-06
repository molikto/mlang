package mlang.compiler;

import org.objectweb.asm.*;

abstract class MethodRunJava {
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

}