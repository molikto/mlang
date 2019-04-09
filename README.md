
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


* when you are not sure, implement the one that is 1. easy to implement 2. restricted 3. enough for now

* roadmap
    * **basics**
        * eta rule
    * coverage checker
        * overlapping patterns
    * mutual recursive functions
    * user defined eliminations
    * evaluation method
    * error reporting
    * record calculus
    * recursive types
        * inductive families of two flavor
        * hit
        * inductive-inductive
        * inductive-recursive
    * cubical features
    * termination checking
    * implicit arguments
    * implicit conversions
    * structural editor
    


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