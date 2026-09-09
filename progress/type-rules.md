# Type-rule sketch: open signatures and parameterized recursive closure

Status: revised design sketch with a relational Rocq specification, not a
soundness proof or an executable source checker. The new entry point is
[OpenSignatures.v](OpenSignatures.v); see [OpenSignatures.md](OpenSignatures.md)
for the build and module map. Its metatheory statements are unproved.
This document supersedes the signature-pair and coercion-free μˢ design in
the earlier sketch. The Haskell checker, original `TypeRules` Rocq modules,
generated PDF, and existing `1.pom`/`2.pom` examples still describe the older
design; their results must not be read as proofs of the rules proposed here.

The design has three layers:

1. **Descriptions** provide strictly positive codes, interpretation,
   enumerations, and the ordinary indexed fixed point from *Elaborating
   Inductive Definitions* (EID).
2. **Open signatures** assemble reusable constructor schemes. A signature
   chooses its own constructors; it does not store a full ambient branch
   function paired with an enabled-label list.
3. **Parameterized closure and elaboration** supply the recursive
   definition at application, using `close F G`. Constructor subtyping
   elaborates to explicit, checked conversions.

The signature and closure rules are a new design, not a transcription of
the constructor-subtyping paper. That paper motivates head restriction;
its coercion-free representation and metatheorems are not assumed here.

## 1. Judgments and universe policy

~~~text
Γ ⊢ t ⇒ A             core synthesis
Γ ⊢ t ⇐ A             core checking
Γ ⊢ t : A             ordinary core typing
Γ ⊢ t ≡ u : A         core definitional conversion

Γ ⊢ e ⇒ A ↝ t         source synthesis, producing core term t
Γ ⊢ e ⇐ A ↝ t         source checking, producing core term t
Γ ⊢ A ⊑ B ↝ c         elaborated subtyping, producing c : A → B
~~~

Here `e` is a source expression, while `t` and `c` are core terms.
Every rule presupposes a valid context and well-formed displayed types.
There is no core constructor-subtyping judgment. Conversion still checks
the same term; source subsumption inserts a conversion:

~~~text
Γ ⊢ t ⇒ A    Γ ⊢ A ≡ B : Setₖ
────────────────────────────── Core-conversion
Γ ⊢ t ⇐ B

Γ ⊢ e ⇒ A ↝ t    Γ ⊢ A ⊑ B ↝ c
──────────────────────────────── Source-subsumption
Γ ⊢ e ⇐ B ↝ c t
~~~

A subtyping derivation must generate an ordinarily typable core function.
The existence of an arbitrary function `A → B` does not itself establish
subtyping: §9 specifies the permitted construction rules.

Use `* = Set₀` and `Type = Set₁`. The concrete description universe in
this sketch stores small parameters and has small interpretations:

~~~text
Γ ⊢ I : Set₀
──────────────────── IDesc-form
Γ ⊢ IDesc I : Set₁

Γ ⊢ D : IDesc I    Γ ⊢ X : I → Set₀
─────────────────────────────────── Interp-form
Γ ⊢ ⟦D⟧ X : Set₀
~~~

Functions and pairs exist at every universe level; mixed-level formation
uses the maximum of the component levels. Existing universe cumulativity,
if enabled, is a core universe rule, not an implicit constructor coercion.
The `πₖ` and `switchₖ` operations must support level 1 because description
codes inhabit `Set₁`. A level-k description universe would require the
corresponding generalization of all formation and interpretation rules;
the notation here does not silently quantify small codes over every level.

One indexed family has one index type `I`. Multiple indices are packaged
into a product, or a dependent Sigma when later indices depend on earlier
ones:

~~~text
packTy []             = 𝟙
packTy [I]            = I
packTy [I₁, ..., Iₙ]  = I₁ × ... × Iₙ
packVal []            = unit
packVal [i]           = i
packVal [i₁, ..., iₙ] = (i₁, ..., iₙ)
~~~

A bare Haskell list is not a dependent telescope: until binder-bearing
entries exist, dependent index telescopes must be supplied as one packaged
term. We write `𝟙` or `1` for the unit type and `unit` for its value.

Core conversion contains alpha equivalence, beta and eta for functions,
pair projections, transparent definition unfolding, and the stated
computation rules for interpretation, enumeration elimination, and
induction. Applied `close` types are opaque: unfolding their shape is an
elimination operation, not an unrestricted type-reduction rule. Bottom
pruning and row widening generate conversions; neither is definitional
equality. In particular, identical constructor names, row inclusion, or
a proposed erasure optimization do not make two types convertible.

## 2. Enumerations

The EID enumeration universe (Figure 2), with suppressed premises explicit:

```text
Γ valid                          Γ valid
──────────────── UId-form        ──────────────── EnumU-form
Γ ⊢ UId : Set₀                   Γ ⊢ EnumU : Set₀

Γ valid    s is a valid identifier
────────────────────────────────── tag
Γ ⊢ 's : UId

Γ valid                          Γ ⊢ t : UId    Γ ⊢ E : EnumU
──────────────── nilE            ────────────────────────────── consE
Γ ⊢ nilE : EnumU                 Γ ⊢ consE t E : EnumU

Γ ⊢ E : EnumU
────────────────── EnumT-form
Γ ⊢ EnumT E : Set₀

Γ ⊢ t : UId    Γ ⊢ E : EnumU     Γ ⊢ t : UId    Γ ⊢ n : EnumT E
──────────────────────────── 0E  ──────────────────────────────── 1+E
Γ ⊢ 0 : EnumT (consE t E)        Γ ⊢ 1+n : EnumT (consE t E)
```

`EnumT E` contains positional witnesses, not stable labels. EID prints the
small (`k = 0`) lookup tuple and eliminator; PomPom needs the
universe-polymorphic lifting because `IDesc I : Set₁`:

```text
πₖ      : (E : EnumU) → (EnumT E → Setₖ) → Setₖ
switchₖ : (E : EnumU) → (P : EnumT E → Setₖ)
        → πₖ E P → (e : EnumT E) → P e
```

EID states these types but not their equations. PomPom needs the standard
completion, for `π` as well as `switch`:

```text
πₖ nilE        P ↦ 1
πₖ (consE t E) P ↦ P 0 × πₖ E (P ∘ 1+)

switchₖ (consE t E) P (p₀, ps) 0      ↦ p₀
switchₖ (consE t E) P (p₀, ps) (1+n)  ↦ switchₖ E (P ∘ 1+) ps n
```

## 3. Constructor identities and local enumeration positions

A reusable constructor has a stable identifier of type `UId` and a
payload scheme. Source aliases resolve to that identifier before row
assembly; distinct scoped declarations must not be confused merely
because their printed names coincide.

An enumeration stores those identifiers, while its inhabitants are local
positions:

~~~text
Label E := EnumT E
~~~

A position is not a constructor's identity across signatures. For example,
`cons` has position `1+0` in `[nil, cons]` and position `0` in
`[cons]`. Both positions can refer to the same reusable constructor.

Name resolution uses the ordinary family:

~~~text
At : (E : EnumU) → UId → EnumT E → Set₀

atHere  : At (consE ℓ E) ℓ 0
atThere : At E ℓ a → At (consE k E) ℓ (1+a)

NoDupEnum : EnumU → Set₀
~~~

Closed enumerations decide `NoDupEnum` by identifier comparison. Surface
rows must resolve each constructor unambiguously and produce distinct
identifiers. The raw EID choice code may still contain duplicate names;
such a code has positional meaning, but named row operations require the
uniqueness premise.

To align a source position `a` and target position `b`, elaboration checks
that both resolve to the same identifier:

~~~text
At Eₛ ℓ a    At Eₜ ℓ b
~~~

There is no ambient enumeration shared by every signature. Widening
between different enumerations builds a tag translation from this
alignment (§9); it never reuses a numeric position without checking its
identity. A missing target label is permissible only when the corresponding
source payload is certified empty.

## 4. Indexed descriptions and their interpretation

The EID codes (Figure 4), checked contextually against an index type,
together with the proposed empty-description code `'⊥`:

```text
Γ ⊢ i : I
──────────────────────── IVar
Γ ⊢ 'var i ⇐ IDesc I

──────────────────────── I1
Γ ⊢ '1 ⇐ IDesc I

──────────────────────── IBottom                         [DESIGN]
Γ ⊢ '⊥ ⇐ IDesc I

Γ ⊢ A ⇐ IDesc I    Γ ⊢ B ⇐ IDesc I
──────────────────────────────────── IProduct
Γ ⊢ A '× B ⇐ IDesc I

Γ ⊢ S : Set₀    Γ ⊢ T : S → IDesc I
──────────────────────────────────── IPi
Γ ⊢ 'Π S T ⇐ IDesc I

Γ ⊢ S : Set₀    Γ ⊢ T : S → IDesc I
──────────────────────────────────── ISigma
Γ ⊢ 'Σ S T ⇐ IDesc I

Γ ⊢ E : EnumU    Γ ⊢ T : EnumT E → IDesc I
────────────────────────────────────────── IChoice
Γ ⊢ 'σ E T ⇐ IDesc I
```

The declarative rules allow any expression of the required function type
for `T` — a lambda, a named definition, or a `switchₖ`.

Interpretation is structural and strictly positive; every `(x:A) × B x`
below is a dependent Sigma:

```text
⟦'var i⟧ X   = X i
⟦'1⟧ X       = 1
⟦'⊥⟧ X       = ⊥
⟦A '× B⟧ X   = ⟦A⟧ X × ⟦B⟧ X
⟦'Π S T⟧ X   = (s:S) → ⟦T s⟧ X
⟦'Σ S T⟧ X   = (s:S) × ⟦T s⟧ X
⟦'σ E T⟧ X   = (e:EnumT E) × ⟦T e⟧ X
```

Here `X : I → Set₀` and `⟦D⟧ X : Set₀`.

The empty type itself can be the empty enumeration, with its eliminator
derived from `switchₖ`:

~~~text
⊥ := EnumT nilE

abortₖ : (A : Setₖ) → ⊥ → A
abortₖ A z = switchₖ nilE (λ _. A) unit z
~~~

We write `abort z` when the target type is determined by the context.
The proposed `'⊥` code computes directly to this small empty type.
An empty choice is also empty, but its interpretation is
`Σ e : EnumT nilE. ⟦T e⟧ X`; that is not definitionally `⊥` under the
displayed rules.

Bottom is not defined by `∀ A. A`: predicatively,
`(∀ A : Setₖ. A) : Setₖ₊₁`. Its universal elimination behavior is supplied
by `abortₖ`, without raising the universe of description interpretations.

## 5. Reference fixed point and structural induction machinery

```text
Γ ⊢ R : I → IDesc I
─────────────────────── MuI-form                              [EID Fig. 4]
Γ ⊢ μᴵ R : I → Set₀

Γ ⊢ i : I    Γ ⊢ xs : ⟦R i⟧ (μᴵ R)
──────────────────────────────────── MuI-in                   [EID Fig. 4]
Γ ⊢ in xs : μᴵ R i
```

The eliminator has the intended EID type (correcting the evident
`μᴵ D`/`μᴵ I R` metavariable slips in the typeset Figure 4):

```text
iinduction :
  (R : I → IDesc I) →
  (P : (Σ i:I. μᴵ R i) → Set₀) →
  ((i:I) → (xs : ⟦R i⟧ (μᴵ R)) →
     iAll (R i) (μᴵ R) xs P → P (i, in xs)) →
  (i:I) → (x : μᴵ R i) → P (i,x)
```

EID gives only this type and refers elsewhere for `iAll`. The
reconstruction intended for PomPom, together with the inductive-hypothesis
builder `hyps` and the computation law, is:

```text
iAll : (D : IDesc I) → (X : I → Set₀) →
       ⟦D⟧ X → ((Σ i:I. X i) → Set₀) → Set₀

iAll ('var j) X x       P = P (j,x)
iAll '1       X unit    P = 1
iAll '⊥       X z       P = 1
iAll (A '× B) X (a,b)   P = iAll A X a P × iAll B X b P
iAll ('Π S T) X f       P = (s:S) → iAll (T s) X (f s) P
iAll ('Σ S T) X (s,x)   P = iAll (T s) X x P
iAll ('σ E T) X (e,x)   P = iAll (T e) X x P

hyps : (D : IDesc I) → (X : I → Set₀) →
       (P : (Σ i:I. X i) → Set₀) →
       ((i:I) → (x : X i) → P (i,x)) →
       (xs : ⟦D⟧ X) → iAll D X xs P

hyps ('var j) X P h x       = h j x
hyps '1       X P h unit    = unit
hyps '⊥       X P h z       = unit
hyps (A '× B) X P h (a,b)   = (hyps A X P h a, hyps B X P h b)
hyps ('Π S T) X P h f       = λ s. hyps (T s) X P h (f s)
hyps ('Σ S T) X P h (s,x)   = hyps (T s) X P h x
hyps ('σ E T) X P h (e,x)   = hyps (T e) X P h x

iinduction R P step i (in xs)
  ↦ step i xs (hyps (R i) (μᴵ R) P (iinduction R P step) xs)
```

These equations and this beta law are a reconstruction required for an
implementation; they are not printed in the EID paper.

The `'⊥` equations extend this reconstruction: an empty-description
payload supplies no recursive fields. The displayed induction machinery
uses small motives. A universe-polymorphic version must be specified
explicitly before using recursive induction into higher universes.

This section records the EID reference construction. New signature
applications use `close` below. The diagonal `close F F` has the same
inductive shape as `μᴵ F`, but this sketch assumes no judgmental equality
between the two separately named formers.

## 6. Open signatures and reusable constructor schemes

A signature is an open, strictly positive datatype expression. The surface
binder denotes its recursive argument:

~~~text
{R :: branches R}       means the open expression λ R. branches R
~~~

For indexed definitions, `R : I → Set₀`; for unit-indexed examples we
write just `R : Set₀`. This is binder notation, not the former pair
`(T, Φ)`. In particular, the bound name does not designate a stored
ambient branch table.

The interpretation-level notation explains the open argument, while the
checked representation remains a description family:

~~~text
Def I := (i : I) → IDesc I                         -- : Set₁

⟦F⟧ X := λ i. ⟦F i⟧ X
~~~

Elaboration replaces each permitted recursive occurrence `R j` with
`'var j`. The body may contain any structure expressible with the strictly
positive description constructors. An arbitrary function
`(I → Set₀) → I → Set₀` is not automatically a valid definition code.
Likewise, returning an `IDesc` from a function with a separate type
parameter does not automatically make recursion through that parameter
positive.

A complete `F i` may contain its own `'σ E T`, including an enumeration
computed from parameters or indices. `Def I` is not indexed by a fixed
external enumeration. The ordinary function `EnumT E → IDesc I` remains
useful inside an individual choice, rather than being the representation
of every complete signature.

For example, the following unit-indexed constructor payload schemes are
ordinary reusable codes:

~~~text
Nil       : IDesc 𝟙
Nil       = '1

Cons      : Set₀ → IDesc 𝟙
Cons A    = 'Σ A (λ _. 'var unit)

Fork      : IDesc 𝟙
Fork      = 'var unit '× 'var unit
~~~

Their interpretations are respectively `𝟙`, `A × R`, and `R × R`.
A constructor declaration associates a stable identifier such as `'cons`
with its scheme. Including that constructor in another signature reuses
the scheme and identity; its recursive field is instantiated by the
recursive definition chosen at that use.

Writing the bodies as labeled sums, possible surface signatures are:

~~~text
_list A      = {R :: nil : 𝟙 | cons : A × R}
_non_empty A = {R :: cons : A × R}
_tree A      = {R :: nil : 𝟙 | cons : A × R | fork : R × R}
~~~

The signatures contain no enabled-label list. Absence is treated as
`'⊥` when comparing rows; a signature may also contain an explicit
`'⊥` branch. The comparison view does not extend the actual enum or
identify the resulting types definitionally.

Row assembly can reuse constructor schemes across unrelated datatypes.
Repeated inclusion of the same identifier must either be rejected or
coalesced after checking payload agreement; conflicting payloads must
never be silently overwritten. The assembled named row has a
`NoDupEnum` witness. List membership and finite-map utilities may help
elaboration, but they are not the representation of a signature.

## 7. Parameterized recursive closure

The proposed core former takes an outer definition and a recursive
definition of the same index type:

~~~text
Γ ⊢ I : Set₀    Γ ⊢ F : Def I    Γ ⊢ G : Def I
───────────────────────────────────────────── Close-form       [DESIGN]
Γ ⊢ close F G : I → Set₀

Γ ⊢ F : Def I    Γ ⊢ G : Def I    Γ ⊢ i : I
Γ ⊢ xs : ⟦F i⟧ (close G G)
───────────────────────────────────────────── Close-in         [DESIGN]
Γ ⊢ in xs : close F G i
~~~

Thus `close F` is a function of the recursive definition. `F` supplies
the outer description; every `'var j` there is interpreted as
`close G G j`. Choosing `G = F` closes ordinary inductive recursion:

~~~text
in : ⟦F i⟧ (close F F) → close F F i
~~~

The shape equation is an isomorphism, mediated by introduction and
elimination:

~~~text
close F G i ≃ ⟦F i⟧ (close G G)
~~~

It is not a definitional unfolding equation. Nor does the ordinary
lambda term `λ fix. F fix` itself create a fixed point: it is an
eta-expansion. The inductive meaning comes from these new formation,
introduction, and elimination rules.

Surface application of definition codes uses this single operation:

~~~text
F(G) ↝ close F G

-- unit-indexed sugar
F(G) ↝ close F G unit
~~~

The expected kind distinguishes definition application from ordinary
function application. A definition passed as `G` has type `Def I`,
not `Set₀`. No second surface operation for closing versus instantiating
is required.

There is no premise that `F` be a restriction of `G`: arbitrary
well-formed definitions of the same index type can be combined. For
example, an outer `cons` scheme can hold a recursive tree. Subtyping is
a separate relation and requires compatible instantiated payloads (§9).

## 8. Elimination and induction for close

One-layer elimination has a universe-polymorphic dependent motive:

~~~text
closeCaseₖ :
  (F G : Def I) → (i : I) →
  (Q : close F G i → Setₖ) →
  ((xs : ⟦F i⟧ (close G G)) → Q (in xs)) →
  (x : close F G i) → Q x

closeCaseₖ F G i Q b (in xs) ↦ b xs
~~~

The introduction in the method's result type is checked at
`close F G i`. Unrolling is a derived operation:

~~~text
unroll F G i x =
  closeCase₀ F G i (λ _. ⟦F i⟧ (close G G)) (λ xs. xs) x

unroll F G i (in xs) ↦ xs
~~~

For recursive induction, fix `G` and let the motive range over the
outer definition as well:

~~~text
P : (F : Def I) → (i : I) → close F G i → Set₀

Pᴳ : (Σ j : I. close G G j) → Set₀
Pᴳ (j, y) = P G j y

step :
  (F : Def I) → (i : I) →
  (xs : ⟦F i⟧ (close G G)) →
  iAll (F i) (close G G) xs Pᴳ →
  P F i (in xs)

closeInd :
  (G : Def I) →
  (P : (F : Def I) → (i : I) → close F G i → Set₀) →
  (step : (F : Def I) → (i : I) →
          (xs : ⟦F i⟧ (close G G)) →
          iAll (F i) (close G G) xs (λ (j,y). P G j y) →
          P F i (in xs)) →
  (F : Def I) → (i : I) → (x : close F G i) → P F i x
~~~

Its proposed computation rule is:

~~~text
closeInd G P step F i (in xs)
  ↦ step F i xs
      (hyps (F i) (close G G) (λ (j,y). P G j y)
            (λ j y. closeInd G P step G j y) xs)
~~~

Recursive hypotheses concern `P G j y`, not `P F j y`, because the
children have type `close G G j`. This distinction is essential for
head-only restrictions. These are proposed primitive rules with outstanding
formation, positivity, computation, and induction obligations; they are not
claimed as an already implemented encoding into the small-index EID core.

Source constructor matching elaborates through `closeCaseₖ` and a
`switchₖ` over the actual outer enumeration. Every exposed position must
receive a branch. A source-omitted branch is compiled to `abort` only
when elaboration constructs an empty-payload witness. An absent label in a
compact row needs no core branch at all. Neutral descriptions or indices
are never evidence of emptiness.

The resulting core has no raw source clause-list selection rule: source
names and duplicate-clause checks are resolved before building the typed
enumeration switch. Nonrecursive observation may return `Setₖ`-valued
results via `closeCaseₖ`; the recursive induction rule above is explicitly
limited to small motives, as is the displayed `iAll` machinery.

## 9. Subtyping elaborates to conversions

### Ordinary conversion, composition, and functions

~~~text
Γ ⊢ A ≡ B : Setₖ
────────────────────────────── Sub-conversion
Γ ⊢ A ⊑ B ↝ λ x. x

Γ ⊢ A ⊑ B ↝ c    Γ ⊢ B ⊑ C ↝ d
───────────────────────────────── Sub-composition
Γ ⊢ A ⊑ C ↝ λ x. d (c x)

Γ ⊢ A : Setₖ
────────────────────────────── Sub-bottom
Γ ⊢ ⊥ ⊑ A ↝ λ z. abortₖ A z
~~~

For dependent function subtyping, the codomain comparison must substitute
the generated domain conversion:

~~~text
Γ ⊢ A′ ⊑ A ↝ c
Γ, x : A′ ⊢ B[c x/a] ⊑ B′ ↝ d
──────────────────────────────────────────────────────────── Sub-Pi
Γ ⊢ ((a : A) → B) ⊑ ((x : A′) → B′)
    ↝ λ f. λ x. d (f (c x))
~~~

Here `d` may depend on `x`. Reusing the old coercion-free codomain rule
without this substitution would be ill typed.

### Bottom-marked branches and row alignment

For a shared enum and branch functions `p, p′`, the initial sufficient
inclusion check is:

~~~text
p ≼ p′  if  ∀ c : EnumT E. p c ≡ '⊥ ∨ p c ≡ p′ c
~~~

This is an elaboration condition, not a core subtyping relation between
terms of function type. It preserves live branch payloads up to
conversion; inclusion of nonempty labels alone is insufficient.

More generally, use the helper judgment:

~~~text
Γ ⊢ D ≼[X] D′ ↝ q

with generated core type:
Γ ⊢ q : ⟦D⟧ X → ⟦D′⟧ X
~~~

Its permitted constructions are:

- Convertible descriptions use identity.
- A certified empty source uses `λ xs. abort (dead xs)`, where
  `dead : ⟦D⟧ X → ⊥` is generated or checked.
- Exposed choices are compared by stable constructor identity. For each
  source position, find the target position with the same identifier and
  check that the live payload types at `X` are convertible. Generate
  `(sourcePosition, xs) ↦ (targetPosition, xs)`.
- A source branch with an empty-payload witness instead eliminates into
  the whole target interpretation. It needs no matching target position.

The choice rule compiles a total source-enum switch. For a live branch it
does not generate a conversion of the payload or recursively traverse it.
Consequently, shared constructor identity alone gives no permission to
change its payload type.

For example, if `D = 'σ Eₛ p` and `D′ = 'σ Eₜ p′`, both enums must
have checked `NoDupEnum` witnesses. A live source branch at `a` requires
some `ℓ,b` with:

~~~text
At Eₛ ℓ a
At Eₜ ℓ b
⟦p a⟧ X ≡ ⟦p′ b⟧ X : Set₀
~~~

A conservative emptiness procedure may recognize `'⊥`, empty choices,
products with an empty component, and exposed choices whose branches all
have empty witnesses. Each success must construct the corresponding
function to `⊥`. This sketch does not infer emptiness of arbitrary
`'Π`, `'Σ`, or `'var` descriptions, and a stuck computation proves
nothing. The procedure is not a decision procedure for semantic
inhabitation.

### Widening closed applications

Both types must use the same recursive definition, up to conversion of
the whole indexed family. Write `X := close G G`:

~~~text
Γ ⊢ F : Def I    Γ ⊢ H : Def I    Γ ⊢ G : Def I    Γ ⊢ i : I
Γ ⊢ F i ≼[close G G] H i ↝ q
──────────────────────────────────────────────────────────── Sub-close
Γ ⊢ close F G i ⊑ close H G i
    ↝ λ x. in (q (unroll F G i x))
~~~

The final `in` is checked at `close H G i`. Recursive payloads retain
the same family `close G G`; only the outer wrapper, label, and certified
impossible branches are handled by the conversion. Taking `H = G`
gives a widening to `close G G i` when the branch inclusion succeeds.
There is no unconditional forgetting rule for arbitrary `close F G`.

Different recursive arguments do not get a subtype relation merely by
sharing constructor schemes. A deep structural conversion between their
recursive families would be an additional feature.

These conversions need not be judgmentally identity, and different local
enums may require actual tag changes. Runtime erasure or a representation
that avoids conversion work requires its own justification. Coercion
coherence is an obligation, not something discharged by calling
signatures phantom types.

## 10. Concrete lists, nonempty lists, and constructor reuse

Let `A : Set₀`. Use the schemes `Nil`, `Cons A`, and `Fork` from §6,
with three independently assembled enums:

~~~text
ListE     = consE 'nil (consE 'cons nilE)
NonEmptyE = consE 'cons nilE
TreeE     = consE 'nil (consE 'cons (consE 'fork nilE))

pList A : EnumT ListE → IDesc 𝟙
pNE A   : EnumT NonEmptyE → IDesc 𝟙
pTree A : EnumT TreeE → IDesc 𝟙

pList A 0         = Nil
pList A (1+0)     = Cons A
pNE A 0           = Cons A
pTree A 0         = Nil
pTree A (1+0)     = Cons A
pTree A (1+(1+0)) = Fork

_list A      = λ _ : 𝟙. 'σ ListE     (pList A)
_non_empty A = λ _ : 𝟙. 'σ NonEmptyE (pNE A)
_tree A      = λ _ : 𝟙. 'σ TreeE     (pTree A)
~~~

Each `p` is an enum switch of the corresponding function type.
All three definitions inhabit `Def 𝟙`. Define:

~~~text
List A     = close (_list A)      (_list A) unit
NonEmpty A = close (_non_empty A) (_list A) unit
Tree A     = close (_tree A)      (_tree A) unit
~~~

The shape isomorphisms are:

~~~text
List A     ≃ 𝟙 + (A × List A)
NonEmpty A ≃ A × List A
Tree A     ≃ 𝟙 + (A × Tree A) + (Tree A × Tree A)
~~~

Core constructors have the following types and local positions:

~~~text
nil : List A
nil = in (0, unit)

cons : A → List A → List A
cons a xs = in (1+0, (a, xs))

consNE : A → List A → NonEmpty A
consNE a xs = in (0, (a, xs))

consTree : A → Tree A → Tree A
consTree a xs = in (1+0, (a, xs))

singletonNE : A → NonEmpty A
singletonNE a = consNE a nil
~~~

The three cons operations are instances of the same constructor scheme;
an expected result type chooses the outer enum and the recursive family.
The singleton terminates because its tail is `List A`.

The nonempty enum has one position, so total observation needs one branch.
The following equations abbreviate `closeCase` followed by its enum
switch:

~~~text
head : NonEmpty A → A
head (in (0, (a, xs))) = a

tail : NonEmpty A → List A
tail (in (0, (a, xs))) = xs
~~~

The generated widening aligns `'cons` at source position `0` with
target position `1+0`:

~~~text
toList : NonEmpty A → List A
toList (in (0, (a, xs))) = in (1+0, (a, xs))

⊢ NonEmpty A ⊑ List A ↝ toList

head (singletonNE a)   ≡ a
tail (singletonNE a)   ≡ nil
toList (singletonNE a) ≡ cons a nil
~~~

No tail is traversed. For `f : List A → B` and `ne : NonEmpty A`,
source `f ne` elaborates to `f (toList ne)`.

Equivalently at the level of possible values, a nonempty outer definition
could retain `ListE` and set its `nil` branch to `'⊥`. Its case
elaboration supplies `abort` for that branch. The compact and padded
representations admit generated conversions in both directions; they are
not definitionally equal and their cons positions differ.

The reverse `List A ⊑ NonEmpty A` check fails on the inhabited `nil`
branch. Also, `List A ⊑ Tree A` does not follow from these rules merely
because both include `nil` and `cons`: their recursive arguments differ.
Taking `close (_non_empty A) (_non_empty A)` would instead require every
tail to be nonempty, producing the inductive shape `N ≃ A × N` with no
finite inhabitants.

## 11. Elaboration and neutral definitions

- **Signature abstraction.** Check the recursive binder and compile its
  strictly positive body to a `Def I`. Resolve constructor schemes and
  assemble each choice's own enum. The previous pair `(T, Φ)` and its
  projections are not part of this representation.
- **Definition application.** Given `F,G : Def I`, elaborate `F(G)`
  to `close F G`, with the unit-index application when appropriate.
  Ordinary lambdas and functions retain ordinary application.
- **Constructor introduction.** Against `close F G i`, expose the outer
  choice of `F i`, resolve the constructor's identity to a local
  position, and check the payload at `⟦branch⟧ (close G G)`.
  The core term is `in (position, payload)`.
- **Existing values.** An already typed variable passed at a wider
  expected type needs the conversion from §9. A fresh constructor can
  often elaborate directly against the expected type.
- **Case coverage.** Compile every exposed source position to an ordinary
  branch or a checked empty elimination. Reject duplicate source clauses.
  Failure to discover a live branch or to compute an index is not an
  emptiness proof.
- **Subtyping.** Prefer direct conversion, then the structural rules and
  certified empty elimination. Resolve rows by identifiers, generate tag
  translations, and check the produced term in the core. Arbitrary search
  for functions between types is not subtyping inference.
- **Neutral terms.** Definitions and row-building expressions may be
  first class and stuck. Use available conversion or explicit checked
  evidence; otherwise postpone the constraint or report it unresolved.
  Neither a guessed label set nor an assumed subtype relation is valid.
- **Caches.** Name tables and evaluated rows are elaborator metadata.
  Cached answers must agree with the same typed alignment and conversion
  checks, including each enum's local positions.

## 12. Proof obligations and source boundary

The companion `OpenSignatures` modules state these rules relationally and
record metatheorems as `Conjecture` declarations. Only closed computation
examples have been checked by proof. Required metatheory work includes:

- **Closure semantics.** Give a model or a well-founded inductive
  construction for `close`, justify its induction principle, and relate
  its diagonal to `μᴵ`. Because `Def I : Set₁`, an encoding that indexes
  a family by all definitions is not automatically an instance of the
  small-index EID `μᴵ` rule.
- **Core metatheory.** Prove formation, strict positivity, substitution,
  preservation, canonical forms, normalization, and consistency for the
  added code and closure rules, including their universe levels.
- **Elaboration soundness.** Prove that checked source terms elaborate to
  well-typed core terms and that every `A ⊑ B ↝ c` produces
  `c : A → B`. Account for substituted coercions in dependent types.
- **Labels and coverage.** Prove agreement of stable identities with
  `At`, uniqueness under `NoDupEnum`, correctness of tag translation,
  and totality of elaborated switches. Reusing a scheme must not confuse
  its local positions or recursive instantiations.
- **Emptiness.** Every recognized dead description must produce the
  claimed empty-elimination function. Bottom marking must not turn
  unknown inhabitation or a neutral term into evidence.
- **Coercions.** Specify a deterministic elaboration policy and prove
  coherence where alternative derivations are intended to agree.
  Identity erasure, representation preservation, and zero-cost widening
  are separate possible results, not assumptions of this design.
- **Algorithmic checking.** Establish the termination and correctness of
  the intended checking fragment. Finite enum alignment is decidable;
  arbitrary semantic emptiness and arbitrary type-function equivalence
  are not being offered as decision procedures.

EID supplies the base description and enumeration constructions in §§2,
4, and 5. The `π`/`switch` equations, `iAll`, `hyps`, and induction
computation laws are the explicit reconstructions needed by this sketch.
The direct `'⊥` code, open-signature elaboration, reusable-constructor
interface, `close`, and coercion-producing rules are the proposed design.

The constructor-subtyping paper supplies motivation for restricting an
outer constructor. Its static label-list rules, phantom-type reading, and
optional φ conversion are not rules of this revised calculus. The
original `TypeRules` Rocq modules and PDF continue to describe the earlier
system; `OpenSignatures` is the separate formalization of this revision.

Primary references (also collected in the
[LaTeX bibliography](../docs/type-rules/open-signatures-references.tex)):

- Pierre-Évariste Dagand and Conor McBride, *Elaborating Inductive
  Definitions* (2012), [arXiv:1210.6390v2](https://arxiv.org/abs/1210.6390).
  Figures 1–4, printed pp. 5–7. Local copy:
  `~/Workspace/Subtyping-Theory/first-class-inductive-types.pdf`.
- Tiago Campos, *First-Class Constructor Subsets for Pattern Matching on
  Indexed Families*, undated working manuscript, Section 2, Rules 1–7 and
  optional βηφ. Local source:
  `~/Workspace/Subtyping-Theory/subindex/LIPIcs_2021_Version_Sample/subtyping_paper.tex`.
- Supporting reference cited by EID for generic induction: James Chapman,
  Pierre-Évariste Dagand, Conor McBride, and Peter Morris, *The Gentle Art of
  Levitation*, ICFP 2010, pp. 3–14,
  [doi:10.1145/1863543.1863547](https://doi.org/10.1145/1863543.1863547)
  ([author’s PDF](https://jmchapman.io/papers/levitation.pdf)).
