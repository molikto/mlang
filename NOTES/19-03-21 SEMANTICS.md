
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
    * **it is said that function type has a positive presentation, look it up, and see if it is dual to the negative presentation of sigma**
    * *[this](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Type+Theory+based+on+Dependent+Inductive+and+Coinductive+Types&btnG=) give a type theory with only inductive and coinductive types. is function type really some special case of coinductive type? then what are the corresponding "special case" of inductive types? or this cannot really apply to Agda-like theory at all?*
    * **can we generalize function types like record types generalize sigma types, they are dual right?**
    * lambda is defined by copattern matching. the same expression can be considered dually, but then it still does't makes total sense (because the need to translate to case tree and losing definitional equality)
    * **definitional equality of lambdas with recursive unfolding, [here](https://cstheory.stackexchange.com/questions/42371/definitional-equality-of-recursive-function-definition-by-infinite-unfolding)?**

* non-recursive record type is generalized sigma type, where the iterative explicit dependency is changed to implicit dependency. can be seen both as positive type or nagetive type, and each has a eta-rule, positive type [with eta (which is subtle)](https://ncatlab.org/nlab/show/product+type#as_a_positive_type) will validate the nagetive type [with eta](https://ncatlab.org/nlab/show/product+type#as_a_negative_type) and vice versa. so non-recursive record type is really both positive and nagetive in a compatible way. 
    * one says it is a inductive type with one constructor in the positive case, this is just because a inductive type has a coproduct-sigma factoring
        * there is no "higher-record type" consider integer defined as differences, there is no projection of the first nat
    * Agda doesn't have eta rule for record types, so in this sense their "projection" rule is just a syntax sugar, which does't support the negative eta rule
        * **what about "Vector are Records Too"?**
        * *can we really allow strictly-positive or even positive in the sense bellow ones?*
        * *if we allow also recursive ones satisfying a positive condition, can we say that they are *intersection* of inductive type and coinductive type, so they can act as both?*

* sum type: is just generalized coproduct type, it is normally a positive type, with eta rule
    * they can be defined with large elimination and boolean, but they are essentially the same thing
    * *can it be viewed as negative type? [here](https://ncatlab.org/nlab/show/sum+type)*
    

* path type, seems to be again a negative type

* (higher) (indexed recursive-)inductive type are seen as positive types. introduction rule is user defined constants. their elimination rule is pattern matching (it should allows [a eta rule like positive record type](https://ncatlab.org/nlab/show/product+type#as_a_positive_type), right? does it? especially for higher one?)
    * categorical logic for basic inductive type
        1. firstly, we can replace a inductive type with a form of `F(X) = (a: A) * (B(a) => X)`, it is a endofunctor in the lccc
        2. then indexed-family is "functor of multiple variable of multiple equations"
        * **is there a inductive definition that is not a polynomial functor??**
    * the rule for what recursion is allowed is "strict positive". this is easy to understand because they allow reductions to W-types (this reduction seems to be just a idea, in intensional type theory, the reduction is [exact](https://ncatlab.org/nlab/show/W-type#wtypes_in_type_theory))
        * **[it is possible to have non-strict but positive ones?](http://vilhelms.github.io/posts/why-must-inductive-types-be-strictly-positive/), also mentioned in 3.2 in "Inductively defined types" by Coquand**
    * **how/in what sense does they reduce to sum-of records? even because there is indexes?**
    * there is a notion of "generalized" and "strict" inductive familes, and usually we are talking about the generalized one (see paper "Indexed Induction-Recursion")
        * can we give a alternative form of generalized inductive type where the equality is definitional and expressed by constraints? this is however not possible, consider:

          ```
          idn : ℕ → ℕ
          idn a = a

          predk : (ℕ → ℕ) → (ℕ → ℕ)
          predk f zero = f zero
          predk f (suc k) = f k

          data Vec {a} (A : Set a) : (ℕ → ℕ) → Set a where
            nill : Vec A idn
            conss : ∀ {n} (x : A) (xs : Vec A n) → Vec A (predk n)
          ```
          it is not like the case of vector, where you can unroll by pattern
          ```
          vec : ℕ → Set
          vec zero = ℕ
          vec (suc n) = (vec n) × ℕ
          ```
          but actually this has been considered before [like here](https://lists.chalmers.se/pipermail/agda/2008/000420.html)
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
            nn : U
            ss : (a : U) → U
            dd : (a : U) → (b : ty zero (ss a) ≡ ty zero (ss a)) → U

          ty _ a i = a
          ```

* induction-induction

* coinductive type (coalgebra approach)
    * **what is a coinductively defined set/type exactly? why there are also the codata approach?**
    * elimination rule is user defined constants
    * introduction rule is copattern matching
    * **why it use the general one but in coinductive case it uses restricted one? what is a indexed-coinductive type?**
    * **what's the definitional equality of coinductive type?**
    * **in what sense is coinductive type the categorical dual of inductive type? can all stuff of inductive type generalize to coinductive type?**
        * *does it has eta? a: stream then a = copattern (head -> head a, tail -> tail a)*
        * *what about higher coinductive type? like [this](https://akuklev.livejournal.com/1211554.html)?*
        * *what about coinduction-recursion, coinduction-coinduction, induction-coinduction? does these even makes sense?*
    * **in a framework with both recursively defined function, inductive types, coinductive types, what's the rules for checking nesting, recursion and references (so called nested inductive type)?**




* more
    * what is **propositional resizing**?
    * what is two level theories?