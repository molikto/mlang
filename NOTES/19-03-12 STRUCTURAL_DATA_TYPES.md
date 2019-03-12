## structural data types?

* in MLTT Pi type has structural equality and can be defined in any context, but record types and inductive types has nominal equality, they are considered an extension of the type theory and can only be defined in a empty context:
    * the idea is you have a logical framework with universes and pi types, then you have a schema to **extend the theory** with data types, and the `succ`, `vec` is considered a "constant" in the theory
        * this works when data type is not parameterized, but when they are, it is a little bit untidy
    * the "schema" itself is not considered "inside" the theory, only the constants they define
    * (definitions in a parameterized modules will be translated to parameterized records and inductive types, so still they can only be defined in a empty context in the core theory)
* an alternative will be treat pi type and data type similarly, if we can make this precise
    * self standing `make` and `construct` expressions. to type check to the proper `record` and `inductive` type, you still need some amount of annotations (just like with `lambda`)

## recursions and nestings?

* then the problem is recursive definitions, if you have recursive functions and put type expressions inside them:
    * ```
      val a = record {b: record { c: nat, d: list(a)}, c: list(a)}
      ```
      how do you validates these expressions? what are the rules?
* consider we introduce a fix operator for data types, and a term level fix operator for all values, then all mutual inductive definitions will be translated to the type level fix operator, and other mutual definitions will be translated to term level fix operator, the difference of the two is distingwished by the syntaxal head
* semantically what can be recursively defined?
    * pi should not be recursively defined `fix a = Nat => a` makes no sense
        * this can be rejected because this is not considered a data type fix, so it is a fix for values, and it fails
        * more importantly all non-lambda recursive value will be considered as a lambda accepting "unit" and appling on "unit", so it will always fails the well-founded test
    * data types consists "records" and "inductive types", the types of them **can** be recursively defined, 
    * what about parameterized data types?
        * instead inductive type should still have their parameters, so non-uniform parameters is allowed: https://coq-club.inria.narkive.com/e3qSfR9G/recursively-non-uniform-parameters-in-inductive-types#post4 `TODO: what's the paper on this?`
    * defining a data type inside a lambda will result in a recursive-inductive definition...

    * does this even makes sense???
      ```
      context = sum {
        empty: context
        cons: context => {
            val type = inductive (context => set) = {
                base: (a: context) => type(a)
                pi: (gamma: context, a: type(gamma), b: type(cons(gamma, a)))
            }
        } => context
      }
      ```

.... it is a **mess**

## separating them all

the idea is the categorical semantics of a recursive data type and a non-recursive one is really not the same thing
* inductive data types -- **must be recursive data type** (this makes sure a recursive and non-recursive data type is never **definitionally** equal)
  * inductive
  * inductive record
* simple data types
  * record -- no need for parameters, because there is not a thing called "non-uniform record or inductive type"
  * sum

* simple data types is structural in the sense you can use them anywhere, because they are just sigma and sums. **they allows type calculus**
  
* the usage of "inductive data types" can appear similar to simple ones, but we restrict syntaxally what term they can contains
    * no calling a recursive function inside (but non-the-less can be defined inside them)
    * no definition of recursive data type/recursive functions is allowed inside
    
  this way the semantics is pretty much the same as when they are defined in empty context

## equality

* for recursive data types, at least tags should not have positional equality, they should have named equality
* but for arguments, this is less sure, inductive types ofc can have positional equality for arguments, but less ture for recursive records
* on the other hand, there is no problem treating them as nominally ineuqal

* for calculus record/sum types we definitely want named equality

## mismatches of data types

* simple data types: dependent record is much richer than sum type, actually, dependent record type (sigma type) is called "dependent sum type" as the dual of dependent function type. and "sum type" is actually called "coproduct type", this is wired anyway
    * thinking sum type as a after thought, maybe we should not bother with it in the first
* should a inductive record think as a special case of inductive type?
    * can we give inductive type a eta rule such that it reduces to traditional eta-rule for record types
    * or should we just don't give them a eta-rule? what's the point of this anyway?
    * should there be higher inductive record types?