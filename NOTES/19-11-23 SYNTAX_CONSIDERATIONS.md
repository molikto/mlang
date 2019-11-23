# surface syntax considerations

syntax maters, even if you have a structural editor, syntax still maters, just see how different the concrete syntax is from the abstract syntax.

syntax also interact with semantics, people tend to create semantical values just for the seek of better syntax, for example `eq_reasoning` in Agda. a good syntax should make users acheive what they want **without semantical overhead**

## detailed examples

### extension methods

if we have a `projection (a: nat) .is_even = ...`, then we can have `projection (a: int) .is_even = ...` and they will not conflict as global definitions, because the projection selection is type-directed. this can be implemented if we project from a non-record-type element or a record-type-with-no-`is_even`-field element, we can search for projections by doing type unification.

this can be extended to accept when left side of `.` is a telescope with implicit parameters, for example `projection (#A: type, l: list(A)).size`, but care is needed when user has also defined a `projection (l: list(nat)).size` then we want to either make a choice that makes sense to users, or forbid this as no sensible choice can be made

this syntax then is translated to a method application. no semantical overhead!

### implicit projections

consider this syntax with `!`
```
define equiv(T A: type): type = record {
  field !f: T ⇒ A
  field component: is_equiv(f)
}
```

what's this? it is like implicit arguments but for record type.

so if `expr: equiv(A, B)` and `t: T`, then `expr(t)` is just `expr.f(t)`, it means for a record type, one field is "principle" and will be immediately projected automately, if you want to access other fields, you need to use `!` operator, `expr!component`

this makes sense as people knows how to "apply" a equivalence, how to "apply" a group homomorphism to a element etc.

this has a simple implementation.

another way to achieve the same result is to define a coercion from `equiv(T, A)` to `T ⇒ A`, comparing the two approach:
* coercion has more syntax overhead, but is much more powerful and flexible
* you can define a functor to act as a function on both object and arrows
* but this means coercion resolution is complicated

#### problematic examples

consider a definition of group:
(`_*_` is not supported by mlang now, but you should get the idea.)
```
define group = record {
  field A: type
  field _*_: A ⇒ A ⇒ A
  field unit: record {
    field !unit: A
    field prop_left: (b: A) ⇒ unit * b ≡ b
    field prop_right: ...
  }
  field inverse: (a: A) ⇒ record {
    field !inverse: A
    field prop_left: inverse * a ≡ unit
    field prop_right: ...
  }
}
```

then you can write `inverse(a) : A` and `inverse(a)!prop_left : inverse(a) * a ≡ unit`


you can even do this for natural number addition! with a proper definition of `+`. you can have `(a + b)` is just addtion, but `(a + b)!cmmutative` as the proof `a + b ≡ b + a`!

but this introduces some semantical overhead, because we create more structures and immediately discard them, also the definition of group is deeper than usually defined.

so not sure if this `!` thing is a good design.


### constructor names
the current behaviour in mlang is constructor names is not exported as definitions, unlike in Agda. for example: `define bool = sum { case true false }`, you need to access the constructor like `bool.true`

this makes global namespace clean, also you have a easier time naming constructors, `set_trunc.squash` and `groupoid_trunc.squash`

also this doesn't have a semantical overhead, because the left side of `.` is not present in the elaborated core term at all!

it does have a syntaxal overhead, in case of parameterized sum, it is even worse (`list(A).nil`).

but we have a shortcut now: `_.nil` means infer the left side of `.`

we want to freely write `true`, `false`, `zero` etc. if we have a syntax `define with_constructors bool = ...`, then we can export the identifiers as global constructor. but it is not well defined for parameterized sum, in case of `nil`, the parameter `A` of `list` must be explicitly given in case of `nil` and in case of `cons` it can be seen as implicit. we can only allow `with_constructors` for non-parameterized sum though. for `list` if user want something similar they can define themselves.

so what implemented now is `define list(A) = sum contextual_constructors { case ... }` in this kind of definitions, if we are checking `nil` against a `list(_)` type, we accpet it even there is no identifier called `nil`, because it is a constructor of the sum we are checking against and this sum has `contextual_constructors`. this is a good middle ground between `with_constructors` and can handle prameterized sums.