
# mlang

## build & run & test

standard SBT project, run `Main` with file name to check, test with standard SBT commands

## code

* dependencies is documented in code, we wish we have more power in controlling this but now we don't
* dotty
    * `==` equality should be used VERY sparsely, it is not known yet we should use multi-universe equality or not
    * no `extends` in core theory!
    * hope one day IntelliJ support and Scala.js support is ok. so we can use Mill, IntelliJ IDEA
    * we want lambda with recievers!!

## mvp

---

first implement without cubical stuff and without implicit argument/subtyping

* when you are not sure, implement the one that is 1. easy to implement 2. restricted 3. enough for now

(in progress)

* **pi**: function types; eta rule; mutually recursively defined lambdas with size-changing termination checker
* pattern matching lambda and coverage checker
    * overlapping and definitional patterns
* **path**: cubical type theory (`TODO: eta for path?`)
* **universe**: non-commutative universe without subtyping with univalance
* data types
    * record type - both negative and positive
        * simple - allows calculus
        * inductive - recursive - no calculus
        * (future: coinductive types)
    * sum type
        * simple
        * computational indexed
        * general indexed
        * hit
* very limited implicit arguments
* coercion subtyping

## maybe roadmap

* first-class sum types (what about defining true/false as sum?)
* all other forms of inductive type mentioned above
* implicit parameters and possibly more liberal unification
* ad-hoc polymorphism
* explicit universe polymorphism with editor helper (Agda style? look it up what it is!!!)
* destructors


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