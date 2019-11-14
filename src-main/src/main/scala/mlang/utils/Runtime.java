package mlang.utils;

import java.lang.reflect.*;

public class Runtime {
  public static String getDescriptorForClass(Class c) {
    if(c.isPrimitive()) {
        if(c==byte.class)
           return "B";
        if(c==char.class)
            return "C";
        if(c==double.class)
            return "D";
        if(c==float.class)
            return "F";
        if(c==int.class)
            return "I";
        if(c==long.class)
            return "J";
        if(c==short.class)
            return "S";
        if(c==boolean.class)
            return "Z";
        if(c==void.class)
            return "V";
        throw new RuntimeException("Unrecognized primitive "+c);
    }
    if(c.isArray()) return c.getName().replace('.', '/');
    return ('L'+c.getName()+';').replace('.', '/');
   }

   public static String getMethodDescriptor(Method m) {
    String s="(";
    for(final Class c:(m.getParameterTypes()))
        s+=getDescriptorForClass(c);
    s+=')';
    return s+getDescriptorForClass(m.getReturnType());
  }
}
