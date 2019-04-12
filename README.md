
# mlang

[![Join the chat at https://gitter.im/mlang-discuess/community](https://badges.gitter.im/mlang-discuess/community.svg)](https://gitter.im/mlang-discuess/community?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge&utm_content=badge)


* when you are not sure, implement the one that is 1. easy to implement 2. restricted 3. enough for now

* roadmap
    * ~~totally unsafe basics~~
    * ~~basic syntax and parser~~
    * ~~mutual recursive functions~~
    * cubical features
    * conversion check
        * eta rule
        * recursive definitions
    * user defined eliminations
    * record calculus
    * evaluator control
        * error reporting
        * reify
            * local unannotated pattern
    * recursive types
        * inductive families of two flavor
        * hit
        * inductive-inductive
        * inductive-recursive
    * implicit arguments
    * implicit conversions
    * small features
        * HTML pretty print
        * naming shadowing
    * coverage checker
        * overlapping patterns
    * termination checking
    * structural editor
        * modules and compile unit
    * universe polymorphism
    * coinductive types
    

## internals

* theory
    * basic for MLTT theory see HoTT book first chapters
    * cubical TT see
         * *Cubical Type Theory: a constructive interpretation of the univalence axiom*
         * *On Higher Inductive Types in Cubical Type Theory*
         * *Higher inductive types in cubical computational type theory*
         * *Syntax and Models of Cartesian Cubical Type Theory*
* implementation
    * the type checker is written in a bidirectional way, some reference is
         * *A simple type-theoretic language: Mini-TT*
         * http://davidchristiansen.dk/tutorials/nbe/
    * but the above reference is not incremental, and to do it incrementally: *Decidability of conversion for type theory in type theory*
    * the idea of using JVM as evaluator is from: *Full reduction at full throttle*



### values

references is considered a redex. and evaluation strategy controls what to reduce.

recursive references is explicitly a different redex.

recursive reference is directly recursive data structure, it is implemented using a clever trick with `var`

the default evaluation strategy will NOT reduce on recursive definitions. this means you need to explicitly unfold them in type checking and conversion checking, this is needed because recursive redex might unfold infinitely

### conversion checking

the conversion checking 

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