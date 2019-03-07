
# mlang

## build & run & test

standard SBT project, run `Main` with file name to check, test with standard SBT commands

## code

* packages and files is indexed by "a-z", resulting in a linear order of files. you 
should be able to read them one by one

## my reading list


* is the size changing used in Agda?
* what is reducibility

### the idea about inductive definitions

1. inductive data type is formed by rules and eliminators: *Inductive Families by Dybjer*
    * scoping of parameters and indexes
    * seems it must be defined under a empty context, or iterated theory, but at least in case of a non-cubical theory, non-empty context is fine (just translate them to parameters)
    * the constructors is strictly positive: recursion must happen as a end of a telescope, trivial one is ordinal induction, or otherwise generalized induction
        * `extension?` also seems in a predictive setting, you can just have non-strict positive, and seems Agda is doing this
    * `extension?` Agda allows recursive happens with non-uniform parameters
    * `extension?` it extends to mutual induction
    * `extension?` [Coq's rules](https://coq.inria.fr/refman/language/cic.html#well-formed-inductive-definitions)
2. to define a function from it, use eliminators
3. recursive pattern matching is introduced. the simplest form is only allows case trees, then covering is easy, then the problem is termination checking
    * *Coquand paper*: well-founded call relation is what makes recursive terminating, some algorithms recognise them is:
       * *A Predicative Analysis of Structural Recursion*
       * *The Size-Change Principle for Program Termination*: is such a wonderful paper!
4. then pattern matching on telescope is introduced and there is another covering checker, i.e. they form a case tree, then we treat them as case trees to do termination checking
5. the *new HIT work by Coquand et al.* "suggested" a schema, and *another work in CMU* extended it to families (seems no parameters?)


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


## misc

* translate to Agda to do correctness checking