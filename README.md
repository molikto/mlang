
# mlang

[![Join the chat at https://gitter.im/mlang-discuess/community](https://badges.gitter.im/mlang-discuess/community.svg)](https://gitter.im/mlang-discuess/community?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)

* next... NOW!
    * what's the "ideal" cubical theory? extension types?
    * understand how implicit variables implemented
    * understand how the more complicated part of a cubical theory implemented
    
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

#### hoas core term `Value`

our value is untyped, higher order abstract syntax

we represent recursive references directly by recursive data structure

because recursive definitions is always terminating, this means all recursive references is guarded. this allows us to directly model recursive reference in a direct way (model recursive references as recursive references in host language, or, hoas for recursive references)

this means non-guarded recursive references will be rejected by evaluator, which is a acceptable minor detail

a recursive type like `nat` is ok because we consider the record and constructor fields all as guarded by a "multi closure", or a closure with a list of values

unlike normalization by evaluation, redux (application, projection, cubical hcom etc.) etc is translated to stuck values. this is because elaborator needs to fill holes by reify from value, and directly normalizing all redux (out side of a closure) will make the term very big

we also consider reference, let expression as redux, but they are redux that don't need any arguments

#### structural types

unlike almost all implementations, we try to treat type definitions structural. validity of recursive definitions can mostly done by syntax restrictions, just like how people makes "nested inductive definitions" works (I suppose). so there is no "schema" of parameterized inductive type definitions, just recursive sum types under a telescope, the "schema" then is a semantics level predicate, not syntax level construction

#### dbi core term `Abstract`

this class is just dbi core term, it exists is because hoas is not composible, you cannot "rebind" a open reference

the conversion from `Abstract` to `Value` is called `eval`, we have currently a compiler by using the Scala compiler directly


#### reductions

we have weak head normal form defined on hoas, `wnhf`, the `app` closure application is call-by-need because we implemented whnf caching


### conversion checking

the conversion checking is type directed conversion checking, but as we use hoas, open variables have a nominal equality, and we don't do index shuffling

the assumptions is: values is well typed, although values don't have type annotations, but for example a stuck term of application, if you know the left hand side has a function type, then you know that right hand side has the type of the domain

so the algorithm is type directed is in this sense: the type is a **assertion** that both terms has a certain type, the level input of `equalType` is a **assertion** that both type is smaller than a certain level, the output of a equality check is a **assertion** that the term is definitional equal.

in case of `equalNeutural`, there is no assertion that the two input is of the same type, it has a return type `Option[Value]` and `Some(v)` is a **assertion** that the two neutral type is of the same type, **and of the same value** and the type is `v`

the conversion checking handles recursive definitions by memorizing equalities between path lambdas, **here we have a assumption all term level recursion is done inside a pattern matching closure** this is somehow inspired by Mini-TT

something similar should be possible with recursive type definitions, in this case, we should treat the recursive references as "open" and do caching


### kan types

context restrictions is done by quoting any **reference** not defined in the restricted context by a restriction. restriction works for all stuff, and it don't further evaluate terms at all. it is the one that calls the restriction will evaluate them further?

we have `hcom`, `coe` as eliminations, in a normalized closed value, they should not appear. they interact with restrictions, just like a path lambda interact with dimensions, then they are inductively defined on all type formers


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