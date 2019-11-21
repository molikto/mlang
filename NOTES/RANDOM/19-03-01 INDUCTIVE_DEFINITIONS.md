
# the idea about inductive definitions

1. inductive data type is formed by rules and eliminators: *Inductive Families by Dybjer*
    * scoping of parameters and indexes
    * seems it must be defined under a empty context, or iterated theory, but at least in case of a non-cubical theory, non-empty context is fine (just translate them to parameters)
    * the constructors is strictly positive: recursion must happen as a end of a telescope, trivial one is ordinal induction, or otherwise generalized induction
    * `extension?` Agda allows recursive happens with non-uniform parameters
    * `extension?` it extends to mutual induction, then to nested inductive types
    * functions application can refer also to the type defined, and normalization is performed so that it produce a type expression in the end
    * `extension?` [Coq's rules](https://coq.inria.fr/refman/language/cic.html#well-formed-inductive-definitions)
    * extending families is induction-recursion
    * induction-induction?
2. to define a function from it, use eliminators
3. recursive pattern matching is introduced. the simplest form is only allows case trees, then covering is easy, then the problem is termination checking
    * *Coquand paper*: well-founded call relation is what makes recursive terminating, some algorithms recognise them is:
       * *A Predicative Analysis of Structural Recursion*
       * *The Size-Change Principle for Program Termination*: is such a wonderful paper!
4. then pattern matching on telescope is introduced and there is another covering checker, i.e. they form a case tree, then we treat them as case trees to do termination checking
5. the *new HIT work by Coquand et al.* "suggested" a schema, and *another work in CMU* extended it to families (seems no parameters?)


## why?

* parameterized inductive type constructor consider themselves don't have parameter as arguments, but as open variables
    ```Agda
    data Opt (x : Set) : Set where
      -- type of none is Opt _x_37
      none : Opt x 
      opt : x → Opt x
    ```