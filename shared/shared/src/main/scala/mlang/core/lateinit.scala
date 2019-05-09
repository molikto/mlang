package mlang.core

import scala.annotation.Annotation

// we document all our `var` usages. almost all locally defined vars is trivial, and only locally meaningful

// essential var values, that used in a way to construct circular data structures and late inited values
// this means these usages is "almost functional", i.e. some thing once set, it never updates
private[core] class lateinit extends Annotation

// a essential mutation field
private[core] class mutable extends Annotation

