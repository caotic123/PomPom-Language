# POMPOM LANGUAGE

In short : Pompom is a cute implementation of a dependently typed language.

Pompom provides an easy unification algorithm, optional constructors, and a strong normalization system, which makes proving with PomPom very easy, for example proving that inserting a element in any position in a list always returns a non-empty list can be encoded like :

```coq
// data List a = | New a (List a) | Empty 
List
  | A :: ~ * ~> * => {(list A) :: |new |empty }. // A list is either a new or a empty constructor

// Data NonEmpty = | New a (NonEmpty a) 
NonEmpty 
  |A :: ~ * ~> * => {(list A) :: |new}. // A list non-empty is list only with new constructor

insert_at // A function that insert a new element in the list and returns a non-empty list 
  |A ls v at :: (A : *) ~ (List A) ~> ~ A ~> ~ Nat ~> (NonEmpty A) => [at of (NonEmpty A)
    |Z => (new A v ls)
    |(S x) => [ls of (NonEmpty A)
      |(empty _) => (new A v (empty A))
      |(new _ head tail) => (new A head (insert_at A tail v x))
    ]
  ].
```
Pompom identifies that function always will return a Non-empty list and accepts insert_at definition, furthermore, you might think that every function defined for a List will not work for a NonEmpty List, however, Pompom uses a subtyping system to check against the patterns, so if you define a function that works for List, it must work also for NonEmpty Lists.

```
length 
  |A ls :: (A : *) ~> ~ (List A) ~> Nat => [ls of Nat
    |(empty _) => Z
    |(new A head tail) => (S (length A tail))
  ].

works_fine
  def my_list_not_empty = ((new Nat Z (empty Nat)) :: (NonEmpty Nat));
  (length Nat my_list_not_empty).
```

Of course the type checker must not allow to use some definition of NonEmpty List on possible empty List, so :

```haskell
last 
  |A ls :: (A : *) ~> ~ (NonEmpty A) ~> A => [ls of A
    |(new A head tail) => [tail of A
      |(empty _) => head
      |(new A head2 tail2) => (last A (new A head2 tail2))
    ]
  ].

do_not_work -- gives a type erros like "Constructor empty do not belongs to NonEmpty Nat"
  def list = ((empty Nat) :: (List Nat));
  (last Nat list).
```

You can read more about our optional constructor later.

# Datatypes (Aka : Symbols)
 
Pompom uses a "stylized" version of The λΠ-calculus, which is a simple dependent type system (simple as COC), but instead of datatypes like in CIC (Coq, Agda, ...), we provide symbols as a "relaxed" way of representing data :

```haskell
Static nat : *.
-- The "*" (Set) and Type universes stores all symbols.
Static Z : nat.
Static S : ~ nat ~> nat.
```

Symbols do not represent any computer behaviour, in fact you can create any natural number with this definition but you cannot derive any recursion or even a predecessor function.

In order to create a valid subset of natural you need to create the definition by using optional constructors :

```haskell
Nat
  {nat :: | Z | S}.
```

We'll need also to change our definition of succ to (We need to do this change because a predecessor of a natural number also needs to be computable) :

```haskell
Static S : ~ {nat :: | Z | S} ~> nat.
-- or  S  : ~ Nat ~> nat.
```

Now, we have unlocked recursion and pattern matching by using Nat as datatype. For example, here the definition of a sum of two natural numbers :

```haskell
+ 
 | n y :: ~ Nat ~> ~ Nat ~> Nat => [n of Nat
  |Z => Z
  |(S x) => Z
].
```

# Dependent types

Pompom supports dependent types via λΠ-calculus, for example, we can encode a Vector indexed with a your length as :

```
Static vector : ~ * ~> ~ Nat ~> *.
Static nil : (A : *) (vector A Z).
Static cons : (A : *) (x : Nat) (y : A) (H : {(vector A x) :: |nil |cons}) (vector A (S x)).

Vector
 | A n :: (A : *) ~> ~ Nat ~> * => {(vector A n) :: |nil |cons}.

```