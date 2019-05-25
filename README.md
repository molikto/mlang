
# mlang

[![Join the chat at https://gitter.im/mlang-discuess/community](https://badges.gitter.im/mlang-discuess/community.svg)](https://gitter.im/mlang-discuess/community?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)


A cubical type theory implementation with implicit arguments, structural record and sum types and more. see roadmap section for details.

see `tests` and `library` folder for sample code. currently `library` contains very little stuff, most is in `tests` folder

## build & run & debug

the project is written in Scala and is a standard SBT project. it can be cross compiled to Scala.js and Scala JVM. currently we are only compiling on JVM.

to compile use `sbt sharedJVM/compile`

the project can be imported into IntelliJ IDEA, and to run/debug, just setup a profile to run `mlang.poorparser.Main` with classpath of module `jvm-shared` (or something like this)

## help wanted

here are some issues that are easy to do, and they are a good way to familiarize yourself with the project, they are marked with `good first issue` in issues list, and in the code, search for `[issue 123]` where `123` is the issue number will lead you to where need to be modified.

if you need more background on a issue, plz go to gitter and just ask.
    
there are other kind of TODOs in the project, they are `LATER`, `TODO`, and `FIXME`, use IntelliJ IDEA to browse them.

## roadmap

* **DONE** totally unsafe MLTT basics
    * function types with eta, record types with eta, inductive types (structural)
    * bidirectional elaborating type checker with mutual recursive definitions
    * readback
    * type directed conversion check with eta and recursive definitions
    * basic `.poor` syntax and parser
* cubical features
    * **DONE** path type
    * **DONE** coe, com, hcom; checking, computation
    * sum type's Kan ops; fcom, higher inductive types
    * univalance
* unification and implicit arguments
    * **DONE** locally scoped meta and very simple solving
    * correctness verification of the whole stuff
       * why unification result doesn't needs to be type checked or am I wrong?
* ~~~~~~~~
* a story for universe, currently type in type
* user defined eliminations
    * user defined implicit right form
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
* **SOUNDNESS** confluence checker (for overlapping patterns)
* **SOUNDNESS** termination checking: currently you don't need modifier `inductively` to write a recursive type, with termination checking, you should not be able to do this
    * relax the syntax check for inductive definitions
* more recursive types
    * inductive families of two flavor
    * inductive-inductive
    * inductive-recursive
    * is [this](https://arend.readthedocs.io/en/latest/language-reference/definitions/hits/#conditions) sound?
* better error reporting
* structural editor
    * modules and compile unit
* universe polymorphism: do we want Agda style (no cumulative), or redtt style, or Coq style?
* coinductive types
* misc
    * translate to Agda to do correctness checking
* math
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

------

**some of bellow is out of date and wrong now, it mainly serves as a place to clear up my thoughts**


### values

#### hoas core term `Value`

our value is untyped, higher order abstract syntax

we represent recursive references directly by recursive data structure, with a trick of mutation and nulls

unlike normalization by evaluation, redux (application, projection, cubical hcom etc.) etc is translated to stuck values. this is because elaborator needs to fill holes by reify from value, and directly normalizing all redux (out side of a closure) will make the term very big

we also consider reference, let expression as redux, but they are redux that don't need any arguments

#### structural types

unlike almost all implementations, we try to treat type definitions structural. validity of recursive definitions can mostly done by syntax restrictions, just like how people makes "nested inductive definitions" works (I suppose). so there is no "schema" of parameterized inductive type definitions, just recursive sum types under a telescope, the "schema" then is a semantics level predicate, not syntax level construction


but for recursive types, they cannot have structural equality, so currently we restrict them to be defined on toplevel, also make them has nominal equality (id'ed `Sum` and `Record` type, just like id'ed pattern expressions)

we don't allow parameterized ones yet. but this is a easy fix

#### dbi core term `Abstract`

this class is just dbi core term, it exists is because hoas is not composable, you cannot "rebind" a open reference

the conversion from `Abstract` to `Value` is called `eval`, we have currently a compiler by using the Scala compiler directly

abstract and values is "type free", let expressions don't have types, etc. the context will have the types when needed. this is natural in a type directed way

I think one thing can be done on Abstract is common expression reduction.

#### reductions

we have weak head normal form defined on hoas, `wnhf`, the `app` closure application is call-by-need because we implemented whnf caching


### conversion checking

the conversion checking is type directed conversion checking, but as we use hoas, open variables have a nominal equality, and we don't do index shuffling

the assumptions is: values is well typed, although values don't have type annotations, but for example a stuck term of application, if you know the left hand side has a function type, then you know that right hand side has the type of the domain

so the algorithm is type directed is in this sense: the type is a **assertion** that both terms has a certain type, the level input of `equalType` is a **assertion** that both type is smaller than a certain level, the output of a equality check is a **assertion** that the term is definitional equal.

in case of `equalNeutural`, there is no assertion that the two input is of the same type, it has a return type `Option[Value]` and `Some(v)` is a **assertion** that the two neutral type is of the same type, **and of the same value** and the type is `v`

the conversion checking handles recursive definitions by memorizing equalities between path lambdas, **here we have a assumption all term level recursion is done inside a pattern matching closure** this is somehow inspired by Mini-TT

something similar should be possible with recursive type definitions, in this case, we should treat the recursive references as "open" and do caching

at least we want to be semi-decidable, this allows more equality to be checked.


### kan types

context restrictions is done by quoting any **reference** not defined in the restricted context by a restriction. restriction works for all stuff, and it don't further evaluate terms at all. it is the one that calls the restriction will evaluate them further?


we have `hcom`, `coe` as eliminations, in a normalized closed value, they should not appear. they interact with restrictions, just like a path lambda interact with dimensions, then they are inductively defined on all type formers

restriction will not reduce on any kind of reference, they are forced by whnf.


### meta variables

#### local representation

conceptually, implicit variables and meta variables are *just* (abstract in the sense before) terms that omitted and can be inferred from other part of the term.

in this sense, each new scoping have a list of definitions like a let expression. and in abstract code, each closure do have a list of meta values, and each usage is also a closed meta reference to them.

for closure, let expression and telescopes in record and sum type, we have 3 different way of representing them in abstract world

we don't explicitly present metas in value world, like we have direct references in value world. it can still be reified, just read it in current closure

#### context representation

we make sure all meta is solved when a context is closed, this way the solved meta can generate abstract properly. see `finishReify` usages

#### mutable metas

having mutable metas and mutable context means our values is mutable. meta solving will mutate the context and the value world.

also adding a new meta will mutate the context. 

this means: unification and type checking is side-effecting. this means one need to be careful when writing these code.

also this means whnf is not stable in some cases (open meta headed ones). so we don't remember unstable ones

other than this, our algorithm is pretty ignorance about metas. open metas is much like a generic variable, closed metas is much like a reference, when evaluation on them doesn't work, we just stuck, when unification doesn't work, just return false. what can be wrong with this? (funny face)

#### meta solving

we use the most simple meta solving algorithm, no constraint etc.

### universe levels

if we allow only toplevel definitions who's closure is all defined to be lifted, then the "up" is entirely transparent, the restriction to top level is because in a parameterized context, you don't know how to up a open variable, but I think one should not count on this?

the problem is for recursive references, you need to deal with lifted open variables

so restriction and up is all defined structurally on values, the difference is: for a closure, a `up` will "de-up" it's parameters, but restriction will also restrict it's parameters
