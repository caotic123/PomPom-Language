# Type-rule sketch: signature-refined inductive families

Status: design sketch, not an implementation or a soundness proof.

This sketch deliberately separates three layers:

1. **EID** — the enumeration and indexed-description universes and the
   ordinary least fixed point: PomPom renditions of *Elaborating Inductive
   Definitions* Figures 1–4, with suppressed well-formedness premises made
   explicit and a predicative universe choice;
2. **SUB** — head-constructor refinement, corresponding to Rules 1–4, 6,
   and 7 of the constructor-subtyping paper; and
3. **BRIDGE** — the glue that spells a SUB signature `{T :: Φ}` in EID
   vocabulary: `T` is a branch-description family and `Φ` a list of
   ambient-typed labels. BRIDGE rules require their own metatheory.

## 1. Judgments and universe policy

```text
Γ ⊢ t ⇒ A         synthesize a type
Γ ⊢ t ⇐ A         check against a type
Γ ⊢ t ≡ u : A     definitional conversion
Γ ⊢ A ⊑ B         subtyping                                    [SUB]
```

Everything else — labels, membership, subset, disjointness, coverage — is
ordinary typing of ordinary terms; no further judgment forms are introduced.

Subtyping is **coercion-free**, exactly as in the subtyping paper: the
subsumption rule re-types the same term, so signatures behave as phantom
refinements with no runtime reflection. No coercion terms, erasure maps, or
coherence laws arise.

```text
Γ ⊢ t ⇒ A    Γ ⊢ A ≡ B : Setₖ                Γ ⊢ t ⇒ A    Γ ⊢ A ⊑ B
────────────────────────────── Conversionφ    ────────────────────────── Subsumption   [SUB]
Γ ⊢ t ⇐ B                                    Γ ⊢ t ⇐ B
```

`⊑` contains `≡` and is transitive.  `≡` throughout is the paper's
`≡βηφ` — Conversionφ is the **default** checking rule (see the end of
this section and Eq-φ in §7).

Use `* = Set₀` and `Type = Set₁`. Although Figure 4 prints `IDesc I : Set`,
Figure 3 prints `Desc : Set₁` and the codes store arbitrary `S : Set₀`; the
predicative PomPom rule is therefore:

```text
Γ ⊢ I : Set₀
──────────────────── IDesc-form
Γ ⊢ IDesc I : Set₁
```

Pairs and functions exist at every `Setₖ` (EID Figure 1); together with the
universe lifting used for `πₖ`/`switchₖ` below (or cumulativity), `Set₁`
pairs may store `Set₀` components. `List`, `0`, `+`, `Dec`, and
propositional `=` are the ordinary small datatypes of the PomPom library,
themselves expressible in the description universe (EID Example 3 style);
their eliminators provide the recursions used below.

One EID index family has one index type `I`. Multiple indices are packaged
into one product; PomPom's current `IData [Term]` and `IVar [Term]` are
surface sugar for this packaging:

```text
packTy []             = 1
packTy [I]            = I
packTy [I₁, ..., Iₙ]  = I₁ × ... × Iₙ
packVal []            = unit
packVal [i]           = i
packVal [i₁, ..., iₙ] = (i₁, ..., iₙ)
```

A bare Haskell list is not a dependent telescope: until binder-bearing
entries exist, dependent index telescopes must be supplied as one packaged
term, or the list form restricted to nondependent components.

Conversion contains capture-avoiding alpha equivalence, beta and eta for
functions, projection computation for pairs (EID Figure 1b), transparent
definition unfolding, and the computation rules for `switchₖ`,
`iinduction`, and `case` stated below.
`in` itself does not reduce. Conversion is a congruence; the implementation
may normalize only as far as a rule needs. Core SUB Rules 3–4 assume only
beta-eta comparison (`T_βη`); the further computation rules are PomPom
conversion policy and must be shown type-preserving. The subtyping paper's
`φ` pruning is adopted as the **default**: `≡` is `≡βηφ`, the smallest
congruence containing the relation above modulo Eq-φ (§7), and the
checking rule is the paper's Conversionφ. A label is pruned only on
positive evidence that its instantiated payload description is uninhabited
— the conservative `AGAINST` analog of §7 — and a stuck description or
index never prunes.

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

## 3. Ambient labels

In the checked core a constructor is its position in the ambient
enumeration — the subtyping paper relies on no particular labeling scheme,
only on decidable constructor equality. The core label type is therefore a
transparent definition, not a package:

```text
Label E := EnumT E
```

The ambient index makes a foreign-family label unrepresentable, and label
equality is decidable by structural induction on positions, exactly like
decidable equality for the naturals:

```text
decide-label : (c d : Label E) → Dec (c = d)
allLabels    : (E : EnumU) → List (Label E)     -- E's positions, in order
```

Printable names belong to elaboration. The resolution relation is an
ordinary inductive family in EID's style, used by the elaborator to turn a
source literal into its position and by the printer to recover the name:

```text
At : (E : EnumU) → UId → EnumT E → Set₀

atHere  : At (consE ℓ E) ℓ 0
atThere : At E ℓ a → At (consE k E) ℓ (1+a)
```

Resolving a printed identifier additionally requires distinct names:

```text
NoDupEnum : EnumU → Set₀
```

A closed enum decides `NoDupEnum` by identifier comparison. Without it, a
positional `Label E` is still meaningful, but resolving a printed
identifier is ambiguous and must not guess a position.

## 4. Indexed descriptions and their interpretation

The EID codes (Figure 4), checked contextually against an index type:

```text
Γ ⊢ i : I
──────────────────────── IVar
Γ ⊢ 'var i ⇐ IDesc I

──────────────────────── I1
Γ ⊢ '1 ⇐ IDesc I

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
⟦A '× B⟧ X   = ⟦A⟧ X × ⟦B⟧ X
⟦'Π S T⟧ X   = (s:S) → ⟦T s⟧ X
⟦'Σ S T⟧ X   = (s:S) × ⟦T s⟧ X
⟦'σ E T⟧ X   = (e:EnumT E) × ⟦T e⟧ X
```

Here `X : I → Set₀` and `⟦D⟧ X : Set₀`.

## 5. The indexed fixed point and its induction principle

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
hyps (A '× B) X P h (a,b)   = (hyps A X P h a, hyps B X P h b)
hyps ('Π S T) X P h f       = λ s. hyps (T s) X P h (f s)
hyps ('Σ S T) X P h (s,x)   = hyps (T s) X P h x
hyps ('σ E T) X P h (e,x)   = hyps (T e) X P h x

iinduction R P step i (in xs)
  ↦ step i xs (hyps (R i) (μᴵ R) P (iinduction R P step) xs)
```

These equations and this beta law are a reconstruction required for an
implementation; they are not printed in the EID paper.

## 6. Signatures and the label-list algebra

A signature is the subtyping paper's `{T :: Φ}`: a complete ambient branch
family together with the list of enabled labels. It is an **ordinary pair**,
not a new type former:

```text
Sig I E  :=  (EnumT E → IDesc I) × List (Label E)          -- : Set₁

{T :: Φ}   :=  (T, Φ)                {T} := {T :: []}
branches S :=  π₀ S                  labels S := π₁ S
Full S     :=  'σ E (branches S)
```

Formation is pairing, nothing else — there is no lifting function between
label lists and signatures. Because pair projections compute judgmentally
(EID Figure 1b), `branches {T :: Φ} ≡ T` and `labels {T :: Φ} ≡ Φ` hold
even when `Φ` is neutral; no primitive fusion equations are needed. The
append reading is derived notation on the same pair:

```text
c \append {T :: Φ}  :=  {T :: c :: Φ}
```

The central ambient-preservation invariant is a one-line consequence:
enabling or disabling labels never changes the description whose fixed
point is the recursive carrier —

```text
Full {T :: Φ} ≡ 'σ E T        for every Φ.
```

The deciding pipeline of `progress/2.pom` lifts bottom-up — constructors,
then constructor lists, then signatures:

```text
Member c []      = 0
Member c (d::cs) = (c = d) + Member c cs

Subset Φ Ψ   = (c : Label E) → Member c Φ → Member c Ψ
Disjoint Φ Ψ = (c : Label E) → Member c Φ → Member c Ψ → 0

decide-member   : (c : Label E) → (Φ : List (Label E)) → Dec (Member c Φ)
decide-subset   : (Φ Ψ : List (Label E)) → Dec (Subset Φ Ψ)
decide-disjoint : (Φ Ψ : List (Label E)) → Dec (Disjoint Φ Ψ)
```

None of this extends the calculus, and none of it is consumed by the
calculus. `Member` is an ordinary type-valued function — list recursion
into `Set₀`, the same large elimination PomPom already checks in library
code — with its two displayed lines computed by match reduction inside
`≡`; `Subset` and `Disjoint` are plain Pi-type abbreviations over it, and
the decision procedures are ordinary programs by list recursion over
`decide-label`. The layering is strict. The core rules of §7 state their
enabled-label conditions directly on evaluated label spines, exactly the
paper's meta side conditions `C ∈ Φ` and `Φ' ⊆ Φ`; they never mention
these library types. The library types internalize the same conditions so
that programs can state and prove the quantified algebra (`union`,
`disjoin`, `UnionInto`). That the two views agree on closed lists —
`decide-member`/`decide-subset` compute to `yes` exactly when the core's
side condition succeeds — is a stated proof obligation (§10), not a
definition.

Union is concatenation with its two inclusion lemmas, and the
signature-level operations act through the projections:

```text
concat : List (Label E) → List (Label E) → List (Label E)

subset-concat-left  : Subset Φ (concat Φ Ψ)
subset-concat-right : Subset Ψ (concat Φ Ψ)

union-sig S R    :=  {branches S :: concat (labels S) (labels R)}
disjoin-sig S R  :=  union-sig S R,  after  Disjoint (labels S) (labels R)
```

Refinement depends on `Φ` only through `Member`, so duplicated labels have
set semantics; canonical de-duplication and `NoDup` canonicality are
routine with `decide-member`. On neutral lists all of these are neutral
computations: they never turn lack of normalization into positive or
negative evidence.

## 7. Signature refinement `μˢ`

For an indexed signature family, the recursive carrier is EID's ordinary
fixed point of the full ambient description; the refinement `μˢ` restricts
only the head constructor.

```text
Γ ⊢ I : Set₀    Γ ⊢ E : EnumU    Γ ⊢ S : (i:I) → Sig I E
───────────────────────────────────────────────────────── Sig-mu
                                              [BRIDGE; SUB Rule 1]
Γ ⊢ μˢ S : I → Set₀

Carrier S := μᴵ (λ i. Full (S i))
```

Formation is liberal, as in the paper: `labels (S i)` may enable a label
whose payload description is uninhabited at `i`; the refinement is then
uninhabited there, which is harmless.

Values of `μˢ S i` are ordinary carrier values — EID's `in`, unchanged.
Enabled membership is a **meta-level side condition**, as in the paper —
not a premise judgment and not a reference to the library `Member` type.
Write `labels (S i) ⇓ Φ` for weak-head evaluation of the enabled list to
its spine, and `c ∈ Φ` for the syntactic search that finds an exposed
element convertible to `c`. On a static list this is literally the paper's
`C ∈ Φ`; evaluation is the only adaptation needed for first-class lists.
Nothing is stored in the term:

```text
Γ ⊢ i : I    Γ ⊢ c : Label E
labels (S i) ⇓ Φ      c ∈ Φ
Γ ⊢ xs : ⟦branches (S i) c⟧ (Carrier S)
───────────────────────────────────────────── Sig-in
                                              [BRIDGE; SUB Rule 3]
Γ ⊢ in (c, xs) : μˢ S i
```

The paper's result-index side condition
`(T Δ'*[u/Δ])_βη = (T Δ*)_βη` is subsumed: `branches (S i)` is already the
branch family at the instance `i`.

Forgetting the refinement and widening the enabled set are pure subtyping —
the term does not change:

```text
Γ ⊢ i : I
───────────────────────── Sig-forget                       [SUB Rule 2]
Γ ⊢ μˢ S i ⊑ Carrier S i

Γ ⊢ (λ i. branches (S₁ i)) ≡ (λ i. branches (S₂ i))
      : (i:I) → EnumT E → IDesc I
labels (S₁ i) ⇓ Φ₁    labels (S₂ i) ⇓ Φ₂    Φ₁ ⊆ Φ₂
Γ ⊢ i : I
──────────────────────────────────────────────────── Sig-sub
                                                     [SUB Rule 4]
Γ ⊢ μˢ S₁ i ⊑ μˢ S₂ i
```

`Φ₁` and `Φ₂` do not occur in the conclusion: they are premise-bound names
for the evaluated `labels` components of the two types already present
there — the same device as the paper's `T_βη` notation, which likewise
names a normal form computed from the rule's subjects. In the paper the
list is part of the type former, so Rule 4 displays it; here the signature
is a term inside `μˢ`, so the rule projects and evaluates instead. When
both families are displayed pairs, that computation is immediate and the
instance reads exactly like Rule 4:

```text
Φ₁ ⊆ Φ₂
──────────────────────────────────────────────────
Γ ⊢ μˢ (λ i. {T :: Φ₁}) i ⊑ μˢ (λ i. {T :: Φ₂}) i
```

The branch premise is global in `i` because recursive `'var` fields of both
sides are interpreted by their carriers, which must be convertible; for two
families built over one shared `T` it holds by projection computation.
`Φ₁ ⊆ Φ₂` is Rule 4's side condition read on evaluated spines: every
exposed element of `Φ₁` occurs, up to conversion, in `Φ₂`, and a neutral
tail of `Φ₁` must be matched by a convertible tail of `Φ₂`. A side
condition that cannot be established is stuck — the rule simply does not
apply — and stuckness is never read as a negative fact. Shared branch
descriptions are invariant: structural
subtyping between different payloads is a separate feature with its own
variance and coercion rules, and must not be obtained from label inclusion.

Function subtyping is the paper's rule, verbatim:

```text
Γ ⊢ A' ⊑ A    Γ, x:A' ⊢ B ⊑ B'
─────────────────────────────────── Pi-sub                 [SUB Rule 6]
Γ ⊢ (x:A) → B ⊑ (x:A') → B'
```

The paper's Rule 5 remains an algorithmic shortcut derivable from
application typing plus subsumption; it is kept out of the declarative
calculus.

Elimination requests branches for a clause list `Ψ` that covers the
enabled labels; coverage is the same evaluated-spine side condition:

```text
Γ ⊢ M : μˢ S i    Γ ⊢ Q : Setₖ
Ψ = (c₁, …, cₘ)    Γ ⊢ cₖ : Label E    the cₖ pairwise distinct
labels (S i) ⇓ Φ      Φ ⊆ Ψ
for each k,
  Γ, xs : ⟦branches (S i) cₖ⟧ (Carrier S) ⊢ Nₖ : Q
──────────────────────────────────────────────────────────── Sig-case
                                              [BRIDGE; SUB Rule 7]
Γ ⊢ case M of Q { cₖ xs ⇒ Nₖ } : Q

case (in (a, xs)) of Q { cₖ xs ⇒ Nₖ }
  ↦ Nₖ[xs]        for the unique k with cₖ = a
```

Distinct labels make the reduct unique. On raw terms — before Sig-case's
distinctness has been checked — the reduct is the *first* clause whose
label is canonically `a`, and the redex fires only once every earlier
clause label is canonical with a distinct position; canonical positions
are normal, so the selection is stable and raw case reduction stays
deterministic even on duplicate-label junk. This is load-bearing:
conversion is an untyped congruence, so a nondeterministic raw case would
let `case (in (a,xs)) of { c ⇒ t ; c ⇒ u }` equate arbitrary terms and
collapse `≡` entirely. On well-typed matches the first match is the
unique match. Coverage is decided whenever the
enabled list evaluates far enough; a stuck coverage check rejects the
match with a diagnostic — the checker never guesses a set. The paper
additionally
restricts `Ψ ⊆ Φ` — no clause outside the signature — which the
implementation should keep as a diagnostic. This case rule intentionally
has a fixed result `Q`, as in Rule 7; dependent index matching still
requires explicit transports.

Pruning an enabled label whose payload is uninhabited (the paper's
`Φok`/`AGAINST`) is the **default**, folded into conversion by Eq-φ —
the paper's `Norm-φ` read on the pair rendition. Because a signature is a
pair term whose projections must keep computing, φ equates the refinement
types, never the pairs:

```text
Γ ⊢ (λ i. branches (S₁ i)) ≡ (λ i. branches (S₂ i))
      : (i:I) → EnumT E → IDesc I
labels (S₁ i) ⇓ Φ₁    labels (S₂ i) ⇓ Φ₂
Φ₁ ↝φ Ψ    Φ₂ ↝φ Ψ          (at instance i)
──────────────────────────────────────────────────── Eq-φ
Γ ⊢ μˢ S₁ i ≡ μˢ S₂ i
```

`↝φ` may drop any exposed label whose instantiated payload description
`branches (S i) c` is demonstrably uninhabited and keeps the rest; a
neutral tail stops pruning. The `AGAINST` analog derives emptiness
positively and conservatively: a `'σ` whose enumeration spine evaluates to
`nilE` (the paper's head-constructor clash), propagated through `'×` and
through every branch of an exposed choice; `'var`, `'1`, `'Π`, and `'Σ`
never prune — the paper's `⊤` "otherwise" clause. In the dependent setting
this remains the rule: failure to normalize an index or signature never
proves impossibility. With Conversionφ, the paper's practical choice
`Ψ = Φok` in Rule 7 is admissible by first converting the scrutinee's type
to the pruned refinement; Sig-case itself keeps its `Φ ⊆ Ψ` coverage.

`μˢ` supplies only this outer analysis. Recursive functions forget the
refinement (Sig-forget) and use `iinduction` over `Carrier S`.

**Operational reading** (as in the paper): under the canonical-forms lemma,
a closed `M : μˢ S i` weak-head-normalizes to `in (c, xs)` with
`Member c (labels (S i))` and `xs : ⟦branches (S i) c⟧ (Carrier S)`.
This is what makes Sig-case's coverage sound, and is a stated proof
obligation.

A carrier value can be re-refined only when the signature demonstrably
enables every ambient position: if `labels (S i)` evaluates to a spine
containing all of `allLabels E`, one layer of case analysis on the outer
position (via `switchₖ`) re-introduces the same value with Sig-in,

```text
coverFull : Carrier S i → μˢ S i        (per such an instance)
```

extensionally the identity. There is no carrier-to-signature downcast
otherwise, no fixed-point covariance from description inclusion, and no
`IDesc` subtyping from label subsets.

## 8. List derivation

```text
ListE = consE 'empty (consE 'new nilE)

emptyLabel := 0    : Label ListE     -- source name 'empty
newLabel   := 1+0  : Label ListE     -- source name 'new
uList : NoDupEnum ListE              -- resolves the source names above

ListBranches A : EnumT ListE → IDesc 1
ListBranches A = switch₁ ListE (λ_. IDesc 1)
                   ('1, ('Σ A (λ_. 'var unit), unit))
-- surface:  switch ListE { 'empty → '1, 'new → 'Σ A (λ value. 'var ()) }

ListSig A     = {ListBranches A :: [emptyLabel, newLabel]} : Sig 1 ListE
NonEmptySig A = {ListBranches A :: [newLabel]}             : Sig 1 ListE

ListS A     = λ _:1. ListSig A
NonEmptyS A = λ _:1. NonEmptySig A
```

Both signatures share the full description judgmentally:

```text
Full (ListSig A) ≡ Full (NonEmptySig A) ≡ 'σ ListE (ListBranches A)
```

The side condition `[newLabel] ⊆ [emptyLabel, newLabel]` is checked
directly on the closed spines (internally, `decide-subset` computes the
same fact), so Sig-sub gives

```text
μˢ (NonEmptyS A) unit ⊑ μˢ (ListS A) unit
```

and the reverse is not derivable. Introduction stores the ambient position
itself — the restricted signature never renumbers `new` to a singleton
position `0`:

```text
Γ ⊢ value : A
Γ ⊢ tail : μˢ (ListS A) unit
Γ ⊢ tail : Carrier (ListS A) unit          (Sig-forget + Subsumption; same term)
labels (NonEmptySig A) ⇓ [newLabel]        newLabel ∈ [newLabel]
──────────────────────────────────────────────────────────
Γ ⊢ in (1+0, (value, tail)) : μˢ (NonEmptyS A) unit
```

The recursive tail is the full carrier, so a non-empty list may end in
`empty`:

```text
in (1+0, (a, in (0, unit))) : μˢ (NonEmptyS A) unit
```

`head` needs one clause (`Ψ = [newLabel]`, coverage decided). There is no
total coercion `μˢ (ListS A) unit → μˢ (NonEmptyS A) unit` without a new
head, a successful refining match on the outer tag, or an optional result.

## 9. Elaboration and the closed fast path

Elaboration bridges source spellings to the checked forms; none of it
extends the type theory.

- **Name resolution.** Given `NoDupEnum E`, a closed literal `'name`
  resolves through `At` to its unique position (`Label E := EnumT E`); the
  checker may cache the host table `κ = {name₀ ↦ 0, …}` for speed. `κ` is
  compiler metadata, never a PomPom term. Open or duplicate-name enums
  require explicit positional labels.
- **Signatures.** `{T :: Φ}` synthesizes `T ⇒ EnumT E → IDesc I`, which
  fixes the ambient `E`, then checks `Φ ⇐ List (Label E)`. Do not force
  `T`'s domain from `Φ`, and do not guess the domain of an unannotated
  lambda. The legacy enum-selection spelling elaborates through the same
  pair: `'σ Ee T ⇝ {T :: enumLabels Ee}`, where `enumLabels` resolves
  `Ee`'s names in the ambient enum of `T` — `Ee` is selection syntax, not
  a second ambient.
- **Mu.** `µ S ⇝ μˢ S` for an indexed family; for unindexed
  `s : Sig 1 E`, `µ s ⇝ μˢ (λ _:1. s) unit`.
- **Introduction.** `in 'c xs` checked against `μˢ S i` resolves `'c` to
  its position `c`, checks the side condition `c ∈ Φ` on the evaluated
  enabled list, and elaborates to `in (c, xs)`; checked against a carrier
  it is plain MuI-in. Both paths produce the same core term, so the
  coherence that a coercive design would have to prove is trivial here.
- **Case.** Clause labels resolve to `Label E`; coverage `Φ ⊆ Ψ` is
  checked on the evaluated enabled list. A stuck check rejects with a
  focused diagnostic; the checker never guesses a set.
- **Closed fast path.** On closed enums and lists everything computes:
  the core side conditions are decided by evaluation plus spine search,
  the internal `decide-*` programs of the algebra reduce to `yes`/`no` in
  agreement with them, and evaluated label lists are their own canonical
  summaries. Caches (`κ`, evaluated label sets)
  must return the same results as computation, may never identify
  structurally different lists as types — only `⊑` relates them — and
  never yield evidence, positive or negative, about a neutral term.

## 10. Proof obligations and source boundary

- **EID supplies** Figures 1–4: the base theory with universe-polymorphic
  pairs and functions, enumerations, `πₖ`/`switchₖ` types, `IDesc`, its
  interpretation, `μᴵ`, `in`, and the displayed type of `iinduction`. The
  `π`/`switch` equations, `iAll` equations, `hyps`, and the `iinduction`
  beta law are reconstructions.
- **SUB supplies** Rules 1–7 for a static constructor list: signature
  formation, forgetting, constructor introduction, subset widening, Pi
  variance, coverage-checked case analysis, the phantom-type reading, and
  the `βηφ` pruning (`Norm-φ`/`Eq-φ`/Conversionφ), adopted here as the
  default conversion.
- **BRIDGE supplies** `Label E := EnumT E` with its decidable equality,
  the elaboration-facing `At` name-resolution family, `Sig I E` as a pair
  of EID data, and the `μˢ` rules, whose side conditions generalize the
  paper's static `C ∈ Φ`/`Φ' ⊆ Φ` only by evaluating the first-class
  label list before the syntactic check.
- **Obligations**: strict positivity of `At` (an ordinary inductive
  family); subject reduction and canonical forms for the `μˢ` layer — the
  paper's claims for its fragment, restated for this rendition;
  normalization and consistency under the predicative universe policy;
  type preservation of the `switchₖ`, projection, `iinduction`, and `case`
  computation rules inside `≡`; soundness of the `AGAINST` analog — a
  derived pruning implies the instantiated payload's interpretation is
  uninhabited — so that Eq-φ is type-preserving; decidability of checking
  for closed programs; agreement of closed-name resolution with `At`; and agreement
  of the internal algebra with the core side conditions — on closed lists,
  `decide-member`/`decide-subset`/`decide-disjoint` (`progress/2.pom`)
  return `yes` precisely when the corresponding spine check succeeds.
- **Discharged by construction** (relative to the earlier coercive,
  inductive-recursive sketch): coercion coherence laws (subtyping no
  longer changes terms), admissibility of an inductive-recursive signature
  block, and normalization of primitive fusion equations (projections
  already compute).

Primary references:

- *Elaborating Inductive Definitions*, Figures 1–4, printed pp. 5–7:
  `~/Workspace/Subtyping-Theory/first-class-inductive-types.pdf`.
- Constructor-subtyping paper, Rules 1–7 and optional `βηφ`, TeX lines
  302–507:
  `~/Workspace/Subtyping-Theory/subindex/LIPIcs_2021_Version_Sample/subtyping_paper.tex`.
