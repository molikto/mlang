package mlang.compiler.semantic

import scala.annotation.Annotation


// we document all our `var` usages. almost all locally defined vars is trivial, and only locally meaningful

// essential var values, that used in a way to construct circular data structures and late inited values
// this means these usages is "almost functional", i.e. some thing once set, it never updates, and it is set at a time
// that don't affect other logic of code, except that it might be circular
private[semantic] class lateinit extends Annotation

// a essential mutation field, once a value of Right(...) is set, it will be stable
private[semantic] class polarized_mutation extends Annotation

private[semantic] class stuck_pos extends Annotation
private[semantic] class type_annotation extends Annotation // see Readme about abstract-surface syntax mismatch
private[semantic] class nominal_equality extends Annotation
