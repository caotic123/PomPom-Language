# POMPOM LANGUAGE

In short: Pompom is an attractive implementation of an extensional dependently typed language for functional programming and for people that want to have fun proving things. Pompom language is so simple that you can implement it yourself just by looking in the source code (We have *only* 1000 lines in the core, you can think that our language is the BASIC language of proof assistants).

Pompom provides an easy unification algorithm, optional constructors, and a strong normalization system (sufficiently fast), which makes proving with PomPom very easy.

For example proving that inserting a element in any position in a list always returns a non-empty list can be encoded like :

```js
// data List a = | New a (List a) | Empty 
List
  | A :: ~ * ~> * => {(list A) :: |new |empty }. // A list is either a new or a empty constructor

// Data NonEmpty = | New a (List a) 
NonEmpty 
  |A :: ~ * ~> * => {(list A) :: |new}. // A list non-empty is list only with new constructor

// A function that insert a new element in the list and returns a non-empty list 
insert_at 
  |A ls v at :: (A : *) ~ (List A) ~> ~ A ~> ~ Nat ~> (NonEmpty A) => [at of (NonEmpty A)
    |0 => (new A v ls)
    |(+1 x) => [ls of (NonEmpty A)
      |(empty _) => (new A v (empty A))
      |(new _ head tail) => (new A head (insert_at A tail v x))
    ]
  ].
```

Pompom identifies that function always will return a Non-empty list and accepts insert_at definition, furthermore, you might think that every function defined for a List will not work for a NonEmpty List, however, Pompom uses a subtyping system to check against the patterns, so if you define a function that works for List, it must work also for NonEmpty Lists.

```js
length 
  |A ls :: (A : *) ~> ~ (List A) ~> Nat => [ls of Nat
    |(empty _) => 0
    |(new A head tail) => (+1 (length A tail))
  ].

works_fine
  def my_list_not_empty = ((new Nat 0 (empty Nat)) :: (NonEmpty Nat));
  (length Nat my_list_not_empty).
```

Of course the type checker must not allow to use some definition of NonEmpty List on possible empty List, so :

```js
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

# Basic syntax

- Definition : ```def_name : expression```, def_name can have any character except for ```':', '(', ')', '.', '|', '~', '>', '{', '}', '=', '[', ']', ';'```
- Type :  ```(x : A) ~> B```, as a function A going to B, or ```~ A ~> B```, when x does not occur in B.
- Lambda : | ```|x ... :: Type => Body```, being x a parameter (or more) and Type the type notation of the lambda.
- Application : ```(f y)```
- Type Notation : ```(expression :: Type)```
- Symbol : ```Static symbol_name : Type```
- Pattern Matching : ```x of Type [ | predicate => body, ...  ]```, being Type the return type of all clauses
- Local definition (only in parsing) : ```def def_name = expr; expr```
- Let : we are lacking :(


# How to run 

The only requisite is [cabal and GHC](https://www.haskell.org/cabal/)

```
in your preferred directory run :
git clone https://github.com/caotic123/PomPom-Language
cd PomPom-Language
cabal install 
May take some time, and after that :
cabal run Kei2 libs/prelude
```
If everything works, you must see a message like : ```Kei checked your file with successful```. *if something goes wrong, submit it*


# How to prove

For example, suppose that you want to prove something simple like 0 + x = x :

```
trivial_refl
  |x :: (x : Nat) ~> (Eq Nat (+ 0 x) x) => __.
```

The "__" is a hole that says what you need to fill, in this case, the proof follows with reflexivity, you can complete [here](libs/challenges.pom) and make you pull request.


# Datatypes (Aka : Symbols)
 
Pompom uses a "stylized" version of The λΠ-calculus, which is a simple dependent type system (simple as COC), but instead of datatypes like in CIC (Coq, Agda, ...), we provide symbols as a "relaxed" way of representing data :

```js
Static nat : *.
// The "*" (Set) and Type universes stores all symbols.
Static 0 : nat.
Static +1 : ~ {nat :: | 0 | +1} ~> nat.
```

Symbols do not represent any computer behaviour, in fact you can create any natural number with this definition but you cannot derive any recursion or even a predecessor function.

In order to create a valid subset of natural you need to create the definition by using optional constructors :

```haskell
Nat
  {nat :: | 0 | +1}.
  -- Syntax : {first the type :: |<Constructors>}
```

We'll need also to change our definition of succ to (We need to do this change because a predecessor of a natural number also needs to be computable) :

```haskell
Static +1 : ~ {nat :: | 0 | +1} ~> nat.
-- or  +1  : ~ Nat ~> nat.
```

Now, we have unlocked recursion and pattern matching by using Nat as datatype. For example, here the definition of a sum of two natural numbers :

```js
+ 
 | n y :: ~ Nat ~> ~ Nat ~> Nat => [n of Nat
  |0 => y
  |(+1 x) => (+1 (+ x y))
].
```

There is no problem representing proofs using only symbols, if you are writing a backend for example to pompom you could use it to erase data in runtime safely.

# Dependent types

Pompom supports dependent types via λΠ-calculus, for example, we can encode a Vector indexed with a your length as :

```haskell
Static vector : ~ * ~> ~ Nat ~> *.
Static nil : (A : *) (vector A Z).
Static cons : (A : *) (x : Nat) (y : A) (H : {(vector A x) :: |nil |cons}) (vector A (S x)).

Vector
 | A n :: (A : *) ~> ~ Nat ~> * => {(vector A n) :: |nil |cons}.

```

And concatenation is enconded like that :

```js
concat 
 | A n m vec vec2 :: concat_type => [vec of (Vector A (+ n m))
      |(cons _ len head tail) => 
        ((cons A (+ len m) head (concat A len m tail vec2)) :: (Vector A (+ (+1 len) m)))
      |(nil _) => (vec2 :: (Vector A (+ 0 m)))
    ].
```

If you have experience with dependent types you might notice the additional type notation, which is not always demanding, In this case, because of unification direction we need to specify to the type checker. *If something is not working as you wish, you can easily appeal to type notation.*

*For people unfamiliar with dependent types* Proofs are also construed using dependent types, for example the commutative property of addition :


```js
x+y≡y+x
 | x y :: (x : Nat) (y : Nat) * => {(≡ nat (+ x y) (+ y x)) :: | refl}.

+_com 
  | x y :: (x : Nat) (y : Nat) (x+y≡y+x x y) => [x of (x+y≡y+x x y)
    |0 => 
      def y≡y+0 = (zero_identity_plus' y);
      (rewrite' nat y y (+ y 0) (refl nat y) y≡y+0)
    |(+1 n) => 
       def x≡y→x+1≡y+1 = (cong nat (+ n y) (+ y n) nat +1 (+_com n y));
       def x+1+y≡x+y+1 = (symmetry nat (+ y (+1 n)) (+1 (+ y n)) (left_succ_nat y n));
       (rewrite' nat (+1 (+ n y)) (+1 (+ y n)) (+ y (+1 n)) x≡y→x+1≡y+1 x+1+y≡x+y+1)
  ].
```

Proving is almost the same approach from other languages (like Idris), but we often represent data differently to enhance the power of optional constructors, for example, the proof that true <> false.

```js
Static unit : *.
Static I : unit.

Unit
  {unit :: |I}.

False
  {unit :: }. // A false is also a Unit type, but it don't have a constructor, it is the same that forall (x : True), x <> I in Coq for example

Falsity |A :: ~ * ~> Type => ~ A ~> False.

bool_false | H :: (Falsity (Eq Bool true false)) => 
     def Bool→* = |b :: ~ Bool ~> * => [b of *
        |true => Unit
        |false => False
     ];
     (eq_rect Bool true false Bool→* H I).
```

You can explore more examples in libs/prelude.kei.

# Implement it for yourself

For now, we don't have a detailed tutorial of "how to do it", but just studying the code and re-implementing it would be appropriated approach (and easy). Nevertheless, we provide a little orientation of how to do it :
![Rules](https://i.imgur.com/zdBnyGI.jpg)  
*We only made a slight modification by extending the universes, Set : Type*.

Implementing λΠ-calculus would be the easiest part, some not mandatory things can help in your implementation. :

- Do not use Bruijn-index/level if you have no intention of using your implementation as a not fun tool
- Prefer representing context as a map, instead of using type notation inside in your tree.
- Do not use the same tree in the parser and the intermediate representation
- Have fun :)

The normalizer is your preference, only for the sake of simplicity is preferred to be not lazy, finally, unification is also of your preference, you could copy from the old Agda unification algorithm (you only need unification of datatype indices, do not go for circle checking or absurd., for example). The subtyping rules of optional constructors are something that can be detailed more with formal rules, but for now, we don't have a formal specification of it (But it's very straightforward, so no worries). 
*If you have any questions please submit it*

# Contribute 
- You can complete the proofs maintained on [libs/chalanges](libs/challenges.pom) and make your pull request 
- You can report bugs
- Construct a backend (?)
- You can do anything that you want to, also :)

# Some other details
- *if you want to see more about this kind of stuff, follow me on [twitter](https://twitter.com/TiagoCa82822459)*.
- Pompom is actualy Kei2 from [Kei](https://github.com/caotic123/Kei)  
- We are aware that our unification system implies in the k axiom, we would love to change for intensional type theory and be compatible with HOTT.
- I think optional constructors can extend to support computations between the patterns, if this can be possible, so deriving, for example, a quotient type using only optional constructors is probably possible (Not talking about hott here).
-  We do want to extend the expressivity to support other higher abstractions.
- Thinking about the backend, We would love to target it in some practical use (like js or smart contracts).
- And yep, the design of everything can change, only for the sake of expressivity. 
- For now, we don't offer a terminating checker either positivity checker.
- Optional constructors are experimental.
- The purpose of this project is because I need a dependently typed language for test automation, but most languages are overcomplex, so I built it..
- If you are struggling to re-implement Pompom or have any questions, please feel free to contact me at camposferreiratiago@gmail.com.

*para o meu trabalho de TCC :(, me libera UFVJM jesus*
