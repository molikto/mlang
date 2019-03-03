
# mlang

## build & run & test

standard SBT project, run `Main` with file name to check, test with standard SBT commands

## code

* packages and files is indexed by "a-z", resulting in a linear order of files. you 
should be able to read them one by one

## what do we want

* this is a PA that focus on the ease to use
    * we will implement records with `with` see `PROPOSALS.md`

## things to learn

* learn the unification and the limitations
    * what's the variants
    * how to combine (and how easy it is) with other features
* how to add implicits to it
* overloading?

## hard things

* recursive types
  * termination checking
     * implicit and explicit sized type
  * various inductive types and checking
     * vectors are records, too
  * pattern matching
     * unordered overlapping patterns
     * view from left
* implicit and explicit universe polymorphism
  * what's the problems with Coq's UP?
* cubical type theory and hits
  * how do they interact with inductive families?


