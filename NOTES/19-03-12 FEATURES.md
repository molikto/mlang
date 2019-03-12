
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
