
# mlang

## build & run & test

standard SBT project, run `Main` with file name to check, test with standard SBT commands

## code

* packages and files is indexed by "a-z", resulting in a linear order of files. you 
should be able to read them one by one

## my reading list


* what is reducibility
* how does a two level system works?
* semantics of induction-recursion?

## open problems

* induction-recursion in cubical types?

## what do we want

this is a PA that focus on the ease to use
* a moderately strong type theory with features for modeling mathematical objects easily
    * general theory: cubical type theory with cumulative universe
    * explicit universe polymorphism with editor inference
        * `TODO` what's the problems with Coq's UP?
    * **we will implement records with `with` see `PROPOSALS.md`**
        * `TODO` *recursive records???* what are they used for? -- how do they interact with record sum
    * simple parameterized higher inductive types
        * `LATER` inductive families (not needed now. the theory combining cubical type is still unclear)
        * `MAYBE` mutually defined inductive types (when we need them)
        * `MAYBE` recursion-induction (when we need them)
        * `MAYBE` induction-induction (when we need them)
        * `MAYBE` special handling for *vectors are records, too*
    * recursive defined lambdas
        * termination checking
        * `LATER` mutual recursion
    * pattern matching
        * **unordered overlapping patterns**
        * `MAYBE` view from left
    * `MAYBE` ad-hoc overloading
    * implicit arguments, unification with Scala-implicit-style coercion
        * we **don't** add general meta-variables now
* **a structural editor that let you to interact with your values**


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


## misc

* translate to Agda to do correctness checking