## elaboration calculus

a bidirational type checker has type signature like this:

```
def check(unchecked: term, type: value): {}

def infer(unchekced: term): { type: value }
```

a elaborating type checker has type signature like this:

```
def check(unchecked: concrete_term, type: value):
  { elaborated: core_term }

def infer(unchecked: concrete_term):
  { type: value, elaborated: core_term }
```

notice the difference between a checker and a elaborator:
* we have a different syntax for concrete term and core term in elaborator, the concrete term is user facing syntax, and core term is the core syntax (what you see in these type theory papers)
* `check` and `infer` additionally produce a elaborated syntax, and the elaboration result is the whole core syntax tree.

the concrete and core syntax have a lot of differences, e.g.:

* surface syntax might contains implicit arguments, the implicit arguments is inserted during elaboration process and it is directed by the type of the function: each function (in core theory) has a boolean indicating if it is a implicit function type
* one concrete syntax form might be elaborated to different core syntax. for example (in mlang)
   * term application and path application have the same form `a(b)`, but they will be elaborated to different core syntax (`App` and `PathApp`) in a type directed way
   * the same syntax form `a.b` is used as projection `pair0.first` and constructor selection `nat.zero` (for record types, `pair.make` where `make` is the single constructor for record types). they have completely different form in core syntax

as we can see, elaboration process is type directed. this has the consequence that if you want some cool elaboration feature, the information needed must exists in the types. this has the unfortunate result to make the core calculus bloated with information not needed by the core calculus, but only needed by the elaboration process. for exmaple Agda and mlang (currently) all save information about if a function is implicit, and this is not needed outside of elaboration.

so I propose a idea of something like this:


```
def check(unchecked: concrete_term, type: value, etype: evalue):
  { elaborated: core_term }

def infer(unchecked: concrete_term):
  { type: value, etype: evalue, elaborated: core_term }
```

so what is this `etype: evalue` thing? it is a parallel calculation that contains *additional* information about the related type, that is only used by the elaboration process and not present in the core theory, so leaving a clean core calculus.

i think `etype` has a simpler dynamic, for example, we can say that after large elimination, `etype` is lost. this is ok because `etype` only provides additional information, the elaboration process can still continue in a type-directed way (rather than type-and-etype-directed)


## thought examples

### example 1

you can cast a value of type function to a type of implicit function: because you are not changing the type, but only the etype


### example 2

we can give a record with different field names, as concrete names only affect elaboration process, in core theory, everything can be just natural numbers. this way we can define additive group and multive group as different etype, but they are of the same type! so you can `cast` between them! this problem is mentioned [here](https://jiggerwit.wordpress.com/2018/09/18/a-review-of-the-lean-theorem-prover/) and I think this is a very clean solution.

### a bigger example

the code bellow makes no sense in any proof assistant now, but read it and see if you can make it precise what it means: 

```
def test(A: type, G K: group(A), g: G, k: K) = 
  pair.make(g * g, k * k)
```

it means (hopefully you agree with me): given two groups defined on the same set, and two element of the two group, return a pair consisting power 2 of the two elements.

but how to make sense for a proof assistant?

first: how to make sense of `g: G`, in Agda it makes no sense, [in Coq](https://coq.inria.fr/refman/addendum/implicit-coercions.html#coercion-to-a-type) it makes sense by saying it means `g: A`. 

then if we use the Coq approach, we have trouble with the two `*` bellow: intuitively we want to use the mulplication in group `G` and `K` respectively, but they have the same type, there is no way we can select a single typeclass!

I'd like it to means `g: A` and `g: A` have same type, but **different `etype`**, and information in `etype` is used in resolving what `*` is used.

*hint: the elaborated result should be `pair.make(G.*(g, g), K.*(k, k))`*


---

TBC.