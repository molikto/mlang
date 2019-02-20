
# mlang

## build & run & test

standard SBT project, run `Main` with file name to check, test with standard SBT commands

## code

* packages and files is indexed by "a-z", resulting in a linear order of files. you 
should be able to read them one by one
* each feature in the changelog will have a pull request, the code diff should be clean and readable

## things to learn

* typed reduction
* readback and error messages
* unification and implicit resolution

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
* cubical type theory
  * how do they interact with inductive families?


