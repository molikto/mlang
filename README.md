
# mlang

[![Join the chat at https://gitter.im/mlang-discuess/community](https://badges.gitter.im/mlang-discuess/community.svg)](https://gitter.im/mlang-discuess/community?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)
    
* roadmap
    * **DONE** totally unsafe MLTT basics
        * function types with eta, record types with eta, inductive types (structural)
        * bidirectional elaborating type checker with mutual recursive definitions
        * readback
        * type directed conversion check with eta and recursive definitions
        * basic `.poor` syntax and parser
    * cubical features
        * **DONE** path type
        * **DONE** coe, com, hcom; checking, computation
        * extension type?
        * sum type's Kan ops; fcom, higher inductive types
        * univalance
    * implicit arguments on the right: *at least I think it is useful, and also it can be seen as a subset of implicit arguments a la Agda, so no harm implementing at all*
        * **QUESTION** what's the problem of unification under restricted context?
        * user defined implicit right form
    * ~~~~~~~~~~
    * user defined eliminations
    * implicit conversions
    * pretty printer (from readback abstract syntax)
    * record calculus
        * one problem is dependency graph introduces syntax stuff in equality
    * small features
        * HTML pretty print
        * naming shadowing
        * non-dependent closures, can we do it so it subtypes?
    * **SOUNDNESS** positivity checker
    * **SOUNDNESS** coverage checker
    * **SOUNDNESS** termination checking
    * more recursive types
        * inductive families of two flavor
        * inductive-inductive
        * inductive-recursive
        * overlapping patterns
        * is [this](https://arend.readthedocs.io/en/latest/language-reference/definitions/hits/#conditions) sound?
    * better error reporting
    * structural editor
        * modules and compile unit
    * universe polymorphism: do we want Agda style (no cumulative), or redtt style, or Coq style?
    * coinductive types
    
    

## internals

* theory
    * basic for MLTT theory see HoTT book first chapters
    * cubical TT see
         * *Cubical Type Theory: a constructive interpretation of the univalence axiom*
         * *On Higher Inductive Types in Cubical Type Theory*
         * *Higher inductive types in cubical computational type theory*
* implementation
    * the type checker is written in a bidirectional way, some reference is
         * *A simple type-theoretic language: Mini-TT*
         * http://davidchristiansen.dk/tutorials/nbe/
    * but the above reference is not incremental, and to do it incrementally: *Decidability of conversion for type theory in type theory*
      * this don't handle recursive definitions, and we use a way inspired by Mini-TT
    * the idea of using JVM as evaluator is from: *Full reduction at full throttle*



### values

we represent recursive references directly by recursive data structure

and application, projection, reference as redex

for example `define a = a` will be of code `val r = RecursiveReference(null); val a = r.deref(); r.value = a; a`

where `deref` is a redex and under normal evaluation rule, it will evaluate to `null` which will be rejected

this means non-guarded recursive references will be rejected by evaluator

for a guarded recursive reference, then it is ok, for example `val r = RecursiveReference(null); val a = Lambda(_ ⇒ r.deref()); r.value = a; a`

when we evaluate `a(something)` we will get `a` again

a recursive type like `nat` is ok because we consider the record and constructor fields as guarded

`eval`, reductions and closures all take a parameter of reduction strategy

so the default reduction strategy has the property:

* it don't accept non-guarded value definitions, which is non-terminating anyway
* it will always fully evaluate to normal forms, **except** under closures, this means the non-guarded part will not have any reference or recursive reference,
and it will be exactly like a theory without recursive reference and references
* one-time substitution is always terminating **?????** (TODO really? assuming we have termination checker, can we have this property???)

renormalize: it is because a closure has been applied to some value that is not normal form, then these values will not be normalized even if you only perform heredity substitution. it is a bit wired.

### conversion checking

the conversion checking compared to the literature is wired, because it doesn't have de Bruijn indices, so it uses a unique id for open variables, so we don't need to do index shuffling, I don't know if this is correct actually.

the assumptions is: values is well typed, although values don't have type annotations, but for example a stuck term of application, if you know the left hand side has a function type, then you know that right hand side has the type of the domain

so the algorithm is type directed is in this sense: the type is a **assertion** that both terms has a certain type, the level input of `equalType` is a **assertion** that both type is smaller than a certain level, the output of a equality check is a **assertion** that the term is definitional equal.

in case of `equalNeutural`, there is no assertion that the two input is of the same type, it has a return type `Option[Value]` and `Some(v)` is a **assertion** that the two neutral type is of the same type, **and of the same value** and the type is `v`

#### how to handle recursive definitions

it seems to me Agda and Mini-TT handles the problem of readback recursive definitions by: when reading back (or conversion checking) pattern matching neutral value, instead of reading back all the cases (add thus ends up in an infinite loop, for example when reading back `(plus a b)` where a, b is open variable), it only reads back an id of the pattern matching lambda, since a pattern matching lambda is uniquely defined by its src position. (about Agda is only guessing, because Agda seems to have a nominal definitional equality for pattern matching) 


it is extended in our case, by also allowing the id to be different, but as an assumption see `Conversion.scala`


### implicit on the right

problems:

* special handle for `refl`
* how to define `reverse`?
    * type predicate `project list(/a/).reverse = `
    * value predicate
    * `\a\≡_{x ⇒ \A[x]\}\b\.reverse = `
cong: `f: /A/ ⇒ /B[A]/, p: /x/ ≡_A /y/, f(x) ≡B(p) f(y)`
* how to make inductive type parameters injective?

we lost the ability to infer type `a: (x) ⇒ f(x) ≡ g(x)` by application

### inductive type

we don't have special syntax for parameterized inductive type, parameters is done by lambdas, and recursion is done by sum + recursion. this saves syntax. we have restrictions though: like inductive type are likely can only be defined in a global context (for example the conversion checking might loop), we don't know if you can define a inductive type in a restricted context. anyway. the idea is inductive definitions is globally defined `define inductively a(...) = sum ...` just this syntax. we can extend latter to parameterized by more telescope etc. the same applies for inductively defined records.

### kan types

context restrictions is done by quoting any **reference** not defined in the restricted context by a restriction. restriction works for all stuff, and it don't further evaluate terms at all. it is the one that calls the restriction will evaluate them further?

we have `hcom`, `coe` as eliminations, in a normalized closed value, they should not appear. they interact with restrictions, just like a path lambda interact with dimensions, then they are inductively defined on all type formers

## math

* quick sort and properties
* symmetry book
* cubical Agda
* Agda stdlib
* Artin's or Lang's *Algebra*
* Agda's test cases and it's issues
* https://ncatlab.org/homotopytypetheory/show/open+problems#higher_algebra_and_higher_category_theory
    * seems interesting: limits problem?
* https://github.com/HoTT/HoTT
* unimath
* the big problems list
* Agda Katas


## misc

* translate to Agda to do correctness checking