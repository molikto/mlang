
* readings to understand semantics of type theory
    * basics
        * category theory : Category Theory in Context
        * abstract algebra: Algebra: Chapter 0, second printing
    * categorial logic
    * ~~algebraic homotopy~~
    * ~~homotopy theory~~


* the semantics of type theory means two things:
    * categorical logic: is to give some axiom, usually some category with more properties that validates type theory
    * specific models: to give a specific set-theoric construction to validate the model
    * one specific model we can have is a term model, then we can determine that it is initial of a type of axiomatic model, such we know that a type theory is equivalent to a categorical logic
        * see [here](https://ncatlab.org/nlab/show/relation+between+type+theory+and+category+theory), especially the initiality of intensional theories is not proofed yet

* categorical logic for dependent types has many different formulations
    * category with families
    * comprehension categories
    * contextual categories
    * ...
    * **how are they related exactly?**

* road to recursive types: what should the value domain of inductive types look like?
    * understand prameterized indexed inductive type
    * then dual
    * understand prameterized indexed higher inductive type
    * then dual
    * understand induction-recursion induction-induction
    * them all!!!


* each type has a
    * introduction rule
    * elimination rule
    * eta-rule

* polarity in type theory
    * it is always that only specifying only one rule all other rule is drived, so if specifiying elimination rule, it is called nagetive, if introduction rule, positive

* duality in type theory
    * some construction/types has dual concepts in categorical semantics, but the way they are dual is not the same... [here](https://www.reddit.com/r/dependent_types/comments/b241if/dual_of_universe_and_identity_types/) are some examples

* function types is seen as nagetively defined, with well-known eta rule
    * it is dual to sigma type in the sense they are left/right adjoint of the pullback functor
        * **is this the duality in the basic sense? seems not??**
        * **can we generalize function types like record types generalize sigma types, they are dual right? (I guess this is not kind of dual...) a way to think of it is to create a model where the pullback functor has adjoint as record type??**
    * function type has a wired looking [positive presentation](https://cstheory.stackexchange.com/questions/16937/funsplit-and-polarity-of-pi-types?rq=1)
    * lambda is defined by copattern matching
    * *what the hell is [this](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Type+Theory+based+on+Dependent+Inductive+and+Coinductive+Types&btnG=)?*
    * **definitional equality of lambdas with recursive unfolding, [here](https://cstheory.stackexchange.com/questions/42371/definitional-equality-of-recursive-function-definition-by-infinite-unfolding)?**
    * **what are categorical semantics for fix points?**
    
* traditionally data types is added as iterated extensions to theory

* non-recursive record type is generalized sigma type, where the iterative explicit dependency is changed to implicit dependency. can be seen both as positive type or nagetive type, and each has a eta-rule, positive type [with eta (which is subtle)](https://ncatlab.org/nlab/show/product+type#as_a_positive_type) will validate the nagetive type [with eta](https://ncatlab.org/nlab/show/product+type#as_a_negative_type) propositionally and vice versa
    * one says it is a inductive type with one constructor in the positive case, this is just because a inductive type has a coproduct-sigma factoring
        * there is no "higher-record type" consider integer defined as differences, there is no projection of the first nat
    * Agda doesn't have negative eta rule for recursive record types, so in this sense their "projection" rule is just a syntax sugar, which does't support the negative eta rule
        * vectors can be seen as records too, becuase they defined a family of non-recursive records. see "Vector are Records Too"?
    * what will go wrong if a recursive record type also has a negative eta rule? [here](https://github.com/agda/agda/issues/402) and [here](https://cstheory.stackexchange.com/questions/42606/what-will-go-wrong-if-a-recursive-record-type-has-a-negative-eta-rule)
        * **so in this sense we should allow recursive records, and they are not seen as a simple generaization of sigma types. but it needs to be seen if they allow record calculus?**

* sum type: is just generalized coproduct type, it is normally a positive type, with eta rule
    * they can be defined with large elimination and boolean, but they are essentially the same thing
    * *can it be viewed as negative type? [here](https://ncatlab.org/nlab/show/sum+type)*
    

* path type, seems to be again a negative type

* (higher) (indexed recursive-)inductive type are seen as positive types. introduction rule is user defined constants. their elimination rule is pattern matching (it should allows [a eta rule like positive record type](https://ncatlab.org/nlab/show/product+type#as_a_positive_type), right? does it? especially for higher one?)
    * categorical logic for basic inductive type
        1. firstly, we can replace a inductive type with a form of `F(X) = (a: A) * (B(a) => X)`, it is a endofunctor in the lccc
        2. then indexed-family is "functor of multiple variable of multiple equations"
        * **is there a inductive definition that is not a polynomial functor?? or what's inductive??**
    * the rule for what recursion is allowed is "strict positive". this is easy to understand because they allow reductions to W-types (this reduction seems to be just a idea, in intensional type theory, the reduction is [exact](https://ncatlab.org/nlab/show/W-type#wtypes_in_type_theory))
        * **[it is possible to have non-strict but positive ones?](http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/), see also [here](https://cstheory.stackexchange.com/questions/21882/example-of-where-violation-of-strict-positivity-condition-in-inductive-types-lea?rq=1), what does this answer means exactly?**
    * general form of inductive families, so the data is `(b, j i)`
      ```
      data D : I → Set where
        C : (a: A) → ((b : B a) → D (j a b)) → D (i a)
      ```
    * there is a notion restricted inductive familes where `i` binds uniformly
      ```
      rdata D : I → Set by
        (a: A i) → ((b : B i a) → D (j i a b)) : D (i)
      ```
        * the Martin-Löf identity type is a gif, but not a rif
        * can we give a alternative form of generalized inductive type where the equality is definitional and expressed by constraints? this is however not possible, because the index can be type that don't allow pattern matching. actually this has been considered before [like here](https://lists.chalmers.se/pipermail/agda/2008/000420.html)
        * how important is it to have this generalized index?? what incovenience will we get? see discuession [here](https://wiki.portal.chalmers.se/agda/pmwiki.php?n=Main.InductiveFamilies). it seems at least essential to [tt in tt](https://github.com/mr-ohman/logrel-mltt/blob/86a0e7c509fd0e8ea3c68b16983627d92006a105/Definition/Conversion.agda)
        * **what if we have a type theory with general indexed family, but annotated reduction rules? (I think this is doable)**
    * the idea of recursive-inductive definition is to define function `T: U => D` and inductive type `U[T]` and only allow `T` occurs in `U` of the form `T(...)`, i.e. application
        * this is rejected as "non-positive" in Agda
          ```
          data U : Set

          ty : (a : U) → a ≡ a

          data U where
            nn : U
            ss : (a : U) → U
            dd : (a : U) → (b : ty ≡ ty) → U

          ty a i = a
          ```
        * this is allowed in Agda
          ```
          data U : Set

          ty : (n : ℕ) → (a : U) → a ≡ a

          data U where
            ss : (a : U) → U
            dd : (a : U) → (b : ty zero (ss a) ≡ ty zero (ss a)) → U

          ty _ a i = a
          ```

    * induction-induction
        * not reducible to inductive types, see [here](https://jashug.github.io/papers/ConstructingII.pdf)
    * higher inductive types inductively add to inductive types paths and squares, also the constructors can mix dimension and reference previous one.
        * (at least now) indexed hit's path constructor also has a index, and there is no heterogeneous equality introduced
        * **the syntax of hit is not entirely worked out see Bob's papers conclusion**. Agda supports more stuff than the two papers, for example identity types, but mostly natural extensions
        * recursive HIT is important. for example to define truncations. see "Semantics of Higher Inductive Types" for examples and one example seems cannot be defined in current Cubical Agda. I guess this is also related **[a non-linearizable example?](https://github.com/agda/cubical/issues/77#issuecomment-478245776)**
    * **can we have unordered pattern matching on all of them?**

* coinductive type (coalgebra approach): elimination rule is user defined constants; introduction rule is copattern matching
    * **what is a coinductively defined set/type exactly? why there are also the codata approach?**
    * coinductive families, compare with restricted inductive families
      ```
      record T : (i: I) → Set where
        a : (A i)
        f : (b : B i a) → T (j i a b)
      ```
    * **what's the definitional equality of coinductive type?**
    * **in what sense is coinductive type the categorical dual of inductive type? can all stuff of inductive type generalize to coinductive type?**
        * *does it has eta? a: stream then a = copattern (head -> head a, tail -> tail a)*
        * *what about higher coinductive type? like [this](https://akuklev.livejournal.com/1211554.html)?*
        * *what about coinduction-recursion, coinduction-coinduction, induction-coinduction? does these even makes sense?*
    * **in a framework with both recursively defined function, inductive types, coinductive types, what's the rules for checking nesting, recursion and references (so called nested inductive type)?**




* more
    * what is **propositional resizing**?
    * what is two level theories? observational type theory?