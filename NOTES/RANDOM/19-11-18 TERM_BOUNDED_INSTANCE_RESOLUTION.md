
typeclass instance resolution is directed by types in Agda and Haskell, consider this statement:


> for set A and G, K as a group on A, g1, g2 is elements of G, and k1, k2 is elements of K, consider the pair (g1 * g2, k1 * k2)

the `*` in the above statement means the multiplication operation in the group G and K depending on the context, the first means `G.*` and the second means `K.*`, but it is perfectly valid for human because we are trained to infer which context is used.

a similar statement cannot be made in Agda though.

```
under (A: type, G K: Group(A), g1 g2: G, k1 k2: K)
  check (g1 * g2 * g1, k1 * k2 * k1)
```

firstly, `g1: G` makes no sense in Agda, but for example in Coq, it can means `g1: G.base`. then even if we can write `g1: G`, you cannot infer which instance should be used for the two `*`.

consider instand of `g1: G` means `g1: G.base`, but it means "`g1: G.base` and `g1` is associated with the context `G`", then we can guide typeclass instance resolution by value instead of type. so each expression in source code is associated with a context-of-association.

for example in `g1 * g2` or `op(g1, g2)` written in prefix operator form (which is what elaborator see after infix operator is parsed), `g1` has a context-of-association of `G`, and type checking `op(g1, g2)` requires, a context (record element) of type `Group(A)` to make sense, so the context-of-association of `op` is set to be `G` because this makes the whole expression typecheck.

what if we have `op(id(g1), g2)`? we need to make id(g1) has the same context-of-association, consider `id`'s type

`id(A: type, a: A): A`

it can be rewritten to be `id(C: Context, a: C): C` so when typechecking `id(g1)`, we will not only infer the result type, but also the result context-of-association, 

`g1 * g2 * g1` is similar but it requires `g1 * g2` has a context-of-association also `G`
