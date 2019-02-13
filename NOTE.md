

# equality for mutual defined functions


## cases we handle as success

```coq
Fixpoint even(a: nat) : bool := 
  match a with
  | O => true
  | S a => odd(a)
  end
with odd(a: nat): bool := 
  match a with 
  | O => false
  | S a => even(a)
  end.

Fixpoint even2(a: nat) : bool := 
  match a with
  | O => true
  | S a => odd2(a)
  end
with odd2(a: nat): bool := 
  match a with 
  | O => false
  | S a => even2(a)
  end.

Fixpoint odd3(a: nat): bool := 
  match a with 
  | O => false
  | S a => even3(a)
  end
with even3(a: nat) : bool := 
  match a with
  | O => true
  | S a => odd3(a)
  end.

Goal even = even2. reflexivity. Qed.

Goal even = even3. reflexivity.  (* fails *)
```

but in Agda

```Agda
nn : Bool → Bool
nn true = false
nn false = true

nn1 : Bool → Bool
nn1 true = false
nn1 false = true

test2 :  nn ≡ nn1
test2 i = nn1 -- fails
```

## what about this??

```Coq
Fixpoint predd(a: nat): nat := 
  match a with
  | O => O
  | S b => predd(b)
  end.

Fixpoint preddd(a: nat): nat := 
  match a with
  | O => O
  | S b => match b with | O => O | S c => preddd(c) end
  end.


Fixpoint predd2(a: nat): nat := 
  match a with
  | O => O
  | S b => preddd(b)
  end.
```