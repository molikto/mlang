
here are some proposals to make writing mathematical definitions and proof in dependent type more pleasant


the ideas might dependent on each other, but they are linearly presented

# proposals

## record type calculus

### specialising on a record field

consider how group is defined in Agda. there are definitions [`isGroup`](https://github.com/agda/agda-stdlib/blob/master/src/Algebra/Structures.agda#L108) and [`Group`](https://github.com/agda/agda-stdlib/blob/master/src/Algebra.agda#L177). 

```
record Group c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 _⁻¹
  infixl 7 _∙_
  infix  4 _≈_
  field
    Carrier : Set c
    _≈_     : Rel Carrier ℓ
    _∙_     : Op₂ Carrier
    ε       : Carrier
    _⁻¹     : Op₁ Carrier
    isGroup : IsGroup _≈_ _∙_ ε _⁻¹
```
```
module Algebra.Structures {a ℓ} {A : Set a} (_≈_ : Rel A ℓ) where

...

record IsGroup (_∙_ : Op₂ A) (ε : A) (_⁻¹ : Op₁ A) : Set (a ⊔ ℓ) where
  field
    isMonoid  : IsMonoid _∙_ ε
    inverse   : Inverse ε _⁻¹ _∙_
    ⁻¹-cong   : Congruent₁ _⁻¹

...
```

this is way more complicated than the informal mathematical definition, where `IsGroup` is implicitly derived from the definition of group.

the reason to separate the two (I think) is to get some definitional equality. for example we want to proof a specific carrier (for example integers `Int`) is a group, then we cannot just return a `Group` but you need to return a [`isGroup` with the carrier `Int` as parameter](https://github.com/agda/agda-stdlib/blob/5e8b6aa91adc6d60606e17db7b579be356f72aec/src/Data/Integer/Properties.agda#L379)


-------

consider an alternative way of doing this. first we define `Group` just as a package (record) of all relevant information

(*these are pseudo-code in a Scala-like syntax. and definitions is not complete*)

```
group = record {
  carrier: set
  law_of_composition: (carrier, carrier) => carrier
  ...
}
```

and for record type, we give it a new reduction rule like this `group(carrier = int)` means the same record type
without the carrier field, and all reference to the carrier field is replaced by the value `int`

one way to consider this is because record type is not a lambda, we can overload the lambda application as if the record type is parametrized by it's fields.

this means the two bellow is definitional equal

```
int_group_type_1 = group(carrier = int)

int_group_type_2 = record {
  law_of_composition: (int, int) => int
  ...
}
```
in this way, when we want to say that integers form a group, we just define a variable `int_group: group(carrier = int)`



example of applying on two fields:

```
category = set + {
  arrows: type
}


category(carrier = base, arrows = obj) // you can apply multiple fields
```



### dependent record intersection


the issue with the aforementioned scheme is we lose the ability to say any group is a monoid, this is present as the `isMonoid` field in `isGroup` record.

the way to fix this is like this:

*(by "set" bellow we means "hSet", not a type like in Agda)*

```
set  = record {
  carrier: type
  is_set: (a b: carrier) => is_prop(x == y)
}

monoid = set + {
  // additional monoid laws
  // notice that you can refer to the name carrier here
  identity: carrier
}

group = monoid + {
  // additional group laws
  inverse = ...
}
```

the code before defines the record `group` on top of record `monoid`. but only this will not be able to give a monoid instance when you have a group, the way to make this work can be

* automately define an implicit conversion `group_is_monoid: group => monoid` when a syntax `monoid + something_else + { ... }` is present
* subtyping (not preferred?)


### failure of intersection

same named fields will be intersected on a intersection of two record type, so the types are required to also have an intersection

```
structure_1 = {
  carrier: type
  a: list(carrier)
}

structure_2 = {
  carrier: type
  a: option(carrier)
}

// will not type check
structure_3 = structure_1 + structure_2 


// will type check, renmaing see bellow
structure_3 = structure_1 + structure_2(renaming a to b) 
```

## record field renaming

both record type and record value will have a new renaming reduction

```
// assuming we have infix operators as field names
abelian_group = group(renaming * to +) + {
  ....
}

```

we still have a implicit conversion from abelian_group to group, and it will rename the record value:

`make` bellow is our syntax to define a record value

```
v1 = abelain_group_as_group(make {
  carrier = int
  + = ...
  ...
})

v2 = make {
  carrier = int
  * = ...
  ...
}
```

the two value above is definitional equal.



## overloading `a : A`

this one is rather simple, because when `g: group`, `g` is not a type, so it cannot be on the right side of `:`. but always in math we talk about "elements" of a group, we actually means elements of the group carrier. 

so we allow `g` appear on the right side, and when we see `g` is not a type, instead of failing type checking, we see if there is a designated field of this record that is a type, like:

```
typeable = record {
  carrier: type
}
set  = typeable + record {
  is_set: (a b: carrier) => is_prop(x == y)
}
```

so, when we type check `g: group, a: g`, seeing `g` is not a type but an instance of `typeable`, we implicitly convert it to `g: group, a: g.carrier`

## constraints


### alternative to specification

how we say that two group is defined on the same carrier?

first we can do it like bellow, using the previous record specification, `unpacking` is yet a new syntax, specifying several fields of a record by another record instance (because `set` is also a record as we defined before)

```
(c: set, g1 g2: group(unpacking c))
```

but what about we give some (definitional) equality constraint to the definition, like bellow, where inside `[]` is the constraint

```
[g1 = g2 on set](g1, g2: group)
```
or
```
[g1.carrier = g2.carrier = g3.carrier](g1 g2 g3: group)
```

then all constraint can be translated to the previous definition without constraints, so in the core type theory there is no modification at all!

*(but what's the good of this? see bellow)*

### constraint inference

the good thing about defining functions with constraints is, a lot of time constraints can be inferred in the unification process, consider the definition of matrix and matrix multiplication

```
matrix = record {
  f: field
  width: nat
  height: nat
  contents: vector(width, vector(height, f.carrier) // or better, just write f instead of f.carrier
}

matrix_multiple[m1.width = m2.height](m1 m2: marix) = ....
```

so now we want to define invertible matrix

```
invertable(m: matrix) = record{ inverse: matrix, eq: matrix_multiple(m, inverse) == matrix_multiple(inverse, m) }
```

you see the problem? this will not type check because `matrix_multiple` not only accept two matrix, it **also needs some constraint met**! but we are not in trouble, on the contrary, we have a blessing:

the constraints can be inferred and filled in by the type-checker, the writer of the function will not need to mention the constraint at all!!

also, we can have a editor functionality to dim the inferred constraint, so readers will be less distracted by less important (because they are derivable information) details!



### conclusion

compared to Agda, seems we declare less implicit parameter (when the parameter is just pass through, or we can just refer it using `a.carrer` syntax), or in the case we can convert them to constraints, we have the ability to not mentioning the implicit parameter in later parameters, and dim the constraint when they are less important.

## implicits

as we say before, the way we make `group` a `monoid` is by implicits, we plan to have more stuff about implicits, and they might be like the one before, is automatic generated


### passing a group as a monoid

```
implicit group_is_monoid(g: group) : monoid = ...

a_function_that_accepts_monoid(a: monoid) = ....

a_group: group = ....

// this should just works
test = a_function_that_accepts_monoid(a_group)
```

### relating to the carrier type

```
implicit product_group(a b: group): group(a.carrier * b.carrier)
```

### just use it as instance argument instead

```
heter_eq = record {
   a: type
   b: type
   h_eq: a => b => bool
}

// inside the function body, the heter_eq is an implicit parameter, so you can just use it like the old typeclass way
some_function(a b: type, implicit heter_eq(a, b)) = ...
```

### conclusion

compared to Agda, it seems we can define less "instance argument" when possible

does it replace the typeclass way of doing things? seems so


# discussion


do you think the proposals are useful? is it widely applicable?

do you think they are ill-defined / what are the potential troubles?

are there already something similar to what mentioned?
