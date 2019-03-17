
we have parameter dependencies in cases of

* pi: (graph)-value
  * lambda: values => value
  * application: value@[]
* record: {graph}-unit
  * make: values
* sum: levels(constructors(string => (graph, boundaries)))
  * construct: (string, values)



theory with two sorts:

Tele =
  (Name: Value, ...)

Value:
  sort: `Tele`, `Set_i`
  pi: Tele => Value
  lambda: `lambda` (Name, ...) -> Value
  record: `record` Tele
  make: `make` (Value, ...)
  ...

in Agda:
funExt : {A : Set} {B : A → Set} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
funExt p i x = p x i

in new Theory: 
fun_ext(domain: Tele, codomain: domain => Set, f g: (ps: domain) => codomain(ps), eq: (ps: domain) => f(ps) == g(ps)) : f == g


funExt(a: Set)(b: A -> Set) (f g: (x: A) => B x)




values  values 

values = [graph - value]

id: (....) => value
id = split (a, b, c) => 

fun_extensitionality



a: Set
a = record {..., ...}

c : a


domain(a: pi): record


cast(a: record, pi: lambda): type




record (..., ...)

meta fun_extensitionality{pi: PiType}(f1, f2: pi){eq: pi.replaceMapsTo(vs => apply(f1, v) == apply(f2, v))}: f1 == f2
fun_ext pi, f1, f2, eq, 

inductive type

enum Value {
    case Graph[T](initials: Seq[(String, Value)], trucks: (preconditions: Seq[String], maps: Map[String, Value] => Value), )
}

(a: b)

enum Value {
    case Pi(Graph[Value])
    case Lambda(Seq[Value] => Value)
    case Record(Graph[Unit])
    case Make(Seq[Value])
    case Sum(String => Graph[Boundaries])
    case Construct(String, Values)
}

function_ext: (a: Graph[value], b: )

{a: b, c: d, ...}(a = 1, c = 2)[c]()

a : (Set_1) => Set_3,
