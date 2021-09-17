# POMPOM LANGUAGE

In short : Pompom is a cute implementation of a dependently typed language. 
Pompom provides an easy unification algorithm, optional constructors, and a strong normalization system, which makes proving with PomPom very easy, for example proving that inserting a element in any position in a list always returns a non-empty list can be encoded like :

```haskell
-- data List a = | New a (List a) | Empty 
List
  | A :: ~ * ~> * => {(list A) :: |new |empty }. -- A list is or a new or a empty constructor

-- Data NonEmpty = | New a (NonEmpty a) 
NonEmpty 
  |A :: ~ * ~> * => {(list A) :: |new}. -- A list non-empty is list only with new constructor

insert_at -- A function that insert a new element in the list and returns a non-empty list 
  |A ls v at :: (A : *) ~ (List A) ~> ~ A ~> ~ Nat ~> (NonEmpty A) => [at of (NonEmpty A)
    |Z => (new A v ls)
    |(S x) => [ls of (NonEmpty A)
      |(empty _) => (new A v (empty A))
      |(new _ head tail) => (new A head (insert_at A tail v x))
    ]
  ].
```
Pompom identifies that function always will return a Non-empty list and accepts insert_at definition, furthermore, you might think that every function defined for a List will not work for a NonEmpty List, however, Pompom uses a subtyping system to check against the patterns, so if you define a function that works for List, it must work also for NonEmpty Lists.

```haskell
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

