in programming languages, there are three implementations for multiple argument functions:


1. direct implementation, functions can take multiple arguments
    * (most of time) allow functions taking zero arguments
        * makes less sense in a pure language
2. curring as functions returning functions
    * only has `A => B` in semantics
    * `(A, B) => C` is defined as `A => (B => C)`
3. curring as functions take tuple as parameters
    * only has `A => B` in semantics
    * `(A, B) => C` is defined as `A * B => C`


most of time 1 is not used in functional languages. currently in proof assistants, only 2 is used. 3 is used in Standard ML.


* 2 good
    * 2 enables free partial application
* 2 bad
    * 2 makes ad-hoc polymorphism harder to use. in a language with ad-hoc polymorphism, the two definition will be duplicated definition, because ad-hoc polymorphism only considers argument type
      ```
      def test(a: Int)(b: Int) = ???
      def test(a: Int) = ???
      ```
* 3 good
    * arguably 3 is more natural with pattern matching. pattern matching is defined on positive types (record, sum), so 3 makes directly implementing pattern matching in semantics level easier (a pattern matching lambda is a lambda defined on positive types). Agda translate to case tree, also Coq, Lean uses eliminator; I don't know any PA implementation of pattern matching in core language; and this will be needed if one want [overlapping patterns](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Overlapping+and+order-independent+patterns+in+type+theory&btnG=)
    * 3 makes it easier to call `funExt f g` where `f` and `g` takes multiple arguments, also `map f [(1,2,3), (4,5,6), (7, 8, 9)]`
* 3 bad
    * not easy to write partial application, we can provide one partial application *macro*, but it will make definitional equality ugly
    * it uses record type, which is not something in basic type theory (most of time only Pi and Sigma), also the syntax is messier: `(A) => B` doesn't create a record type, but `(A, B) => C` does
    
    
the problem of 2 and 3 is a problem of syntax. 

what about mixed case? it forces the definition more principle with what calling convention should be used


* `(A) => B` equals `A => B`, called with `f(a)`
* `(A, B) => C` equals `A * B => C` called with `f(a, b)`, or `val c = (a, b); f(c)`
* `(A; B) => C` equals `A => B => C` called with `f(a; b)` or `f(a)(b)` or `f(a)`
* `(A, B; C, D) => E` equals `A * B => C * D => E` called with `f(a, b; c, d)` or `f(a, b)`
* `{a: A, b: B} => C` calls with `f(a = some, b = some)`

------

anyway. it might be annoying to think what convention should be used to call a function, and one just want to use Agda/Haskell/Coq style currying. non-the-less Agda have pattern matching, but being able to have ad-hoc overloading (for some functions) seems a nice add-on from OO languages.
     
    




