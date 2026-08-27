# PomPom design context

## Open goal — replace `Constr` with first-class signatures

- [ ] Deprecate `Constr Term [Term]` as the core representation of optional
  constructors. Keep it only as temporary surface compatibility while
  definitions using `{T :: |c ...}` are migrated.
- [ ] Represent a signature as an ordinary pair over the EID universe,
  written with the subtyping paper's brace notation:
  `Sig I E := (EnumT E → IDesc I) × List (Label E)`, with
  `{T :: Φ} := (T, Φ)`. Formation is pairing, nothing else: there is no
  separate signature universe, no inductive-recursive block, and no lifting
  function between label lists and signatures. `{T} := {T :: []}` and
  `c \append {T :: Φ} := {T :: c :: Φ}` are derived notation on the pair.
- [ ] Treat `T` as an ordinary dependent expression (a lambda, reference,
  or elaborated `switch`), not as a list of normal-form constructor
  symbols. A `switch E_ambient` may safely handle more labels than `Φ`
  enables.
- [ ] Retain EID's ordinary indexed fixed point `μᴵ` internally. Surface
  `Mu` uniformly elaborates a signature family `(i:I) → Sig I E` to `μˢ`;
  `s : Sig 1 E` has the usual Unit-indexed sugar. Recursive occurrences
  come from the full ambient `μᴵ` carrier. Subtyping is coercion-free, so
  no erasure map is inserted anywhere: the same term inhabits the
  refinement and the carrier.

### Signatures in the core

The checked core adds no signature type former. A signature is a pair of
EID data:

```text
Sig I E   := (EnumT E → IDesc I) × List (Label E)
{T :: Φ}  := (T, Φ)
branches  := π₀        labels := π₁
Full S    := 'σ E (branches S)
```

Pair projections compute judgmentally, so `branches {T :: Φ} ≡ T` and
`labels {T :: Φ} ≡ Φ` hold even for a neutral `Φ`; the old primitive
"fusion" equations are no longer needed. Enabling or disabling labels
never changes `Full S`: `Full {T :: Φ} ≡ 'σ E T` for every `Φ`.

`Label E := EnumT E`: in the core a constructor is its position in the
ambient enumeration, with decidable equality by structural induction —
the subtyping paper relies on no labeling scheme beyond decidable
constructor equality. Printable names belong to elaboration: `At E ℓ a` is
the ordinary proof family saying that name `ℓ` sits at position `a` of
`E`, and a closed literal resolves through it (`NoDupEnum` required) or is
rejected as foreign.

Enabled membership is list membership — there is no separate `Enabled`
family. The core rules check it as the paper's meta side conditions:
evaluate the enabled list and search its spine (`C ∈ Φ`, `Φ' ⊆ Φ`); they
never consume a library proof. The `Member`/`Subset`/`Disjoint` types of
`progress/2.pom` internalize the same conditions for the quantified
algebra, and the two views must agree on closed lists. Repeated
labels have set semantics because refinement depends on `Φ` only through
`Member`. On closed lists these relations are decided by computation; on
neutral lists they remain neutral computations, and the checker must never
approximate them by a guessed host set or fabricate a positive or negative
proof.

The complete type-rule sketch and its source boundary are recorded in
[`progress/type-rules.md`](progress/type-rules.md).

### Closed canonical labels and `switch`

Closed name resolution computes the host table `κ`: for
`ListE = ['empty,'new]`, `{empty ↦ 0, new ↦ 1}`. A restricted signature
keeps ambient tags — `{new}` inherits tag `1`; it is never renumbered to a
singleton position `0`. `κ` exists only in the elaborator; on the general
path the `Label` value itself carries the ambient witness, so no
`EnumT E_small` coercion or enum embedding exists anywhere.

`switch E_ambient` remains total over the full enumeration, while a
restricted signature exposes only its `Member` relation. Closed match
coverage is decided; open coverage is an explicit `Subset` proof, never
guessed from the branches a `switch` happens to handle.

Because the predicative policy places `IDesc I : Set₁`, `πₖ`/`switchₖ`
must be universe-polymorphic (or provide a `Set₁` instance); EID's printed
small eliminator alone cannot define `ListBranches`.

### Quantified signature-algebra goal

[`progress/2.pom`](progress/2.pom) is a goal program for the new signature
system, not an encoding through the current `Constr`, `Static`, or product
library. Its operations consume and produce `Sig I E` pairs and
`List (Label E)` proofs directly; there is no `SignatureSelection`,
`AmbientSignature`, `CanonicalSignature`, or proof-signature wrapper.

Deciding lifts bottom-up: constructors first (`decide-label`, position
induction), then constructor lists (`Member`, `Subset`, `Disjoint` with
their decision procedures, by list recursion), and finally signatures,
where the operations act through the projections:

```text
decide-sig-subset S R    = decide-subset (labels S) (labels R)
union-sig   S R          = {branches S :: concat (labels S) (labels R)}
disjoin-sig S R          = union-sig S R,  after
                           Disjoint (labels S) (labels R)
```

Union consumes and produces `Sig` values and comes with the theorem that
both operands include into it (`subset-concat-left/right`); `disjoin` is
union gated by a `Disjoint` proof, with `decide-disjoint` the
proof-producing decision procedure. Duplicates are harmless — refinement
consults a list only through `Member` — so canonical de-duplication is
routine and omitted. The implication-shaped notation in `progress/2.pom`
is sugar for the two inclusions into a chosen result:

```text
S =>sig R =>sig U  :=  SigSubset S U × SigSubset R U
SigSubset S R      :=  Subset (labels S) (labels R)
```

Its inhabitants are ordinary subset proofs; branch-family agreement is
judgmental because both sides are pairs over the same `T`.

### Ambient-aware `Mu`

`μˢ` is a **head-constructor refinement** of the ambient recursive family:

```text
Carrier S = μᴵ (λ i. Full (S i))
```

`μˢ S i` exposes one enabled outer label while every recursive `'var`
field is interpreted by `Carrier S`. Introduction checks the paper's
`C ∈ Φ` side condition on the evaluated enabled list and elaborates
`in 'c payload` to `in (c, payload)` — EID's `in`, unchanged; the side
condition is
checked, not stored, so the refinement is a phantom type exactly as in the
subtyping paper, and `μˢ S i ⊑ Carrier S i` re-types the same term. A
recursive payload supplied at `µ (List A)` is accepted at the carrier by
subsumption with no inserted coercion.

If `µ` instead took the ordinary fixed point of only the enabled labels,
every tail would also have to start with those labels and a finite list
could never end in `empty`. That would be deep recursive subtyping, not
the head-only behavior of the paper; the ambient carrier interpretation is
part of `µ`'s contract.

### Signature subtyping

For two signature families over judgmentally equal branch families, fewer
enabled labels form the narrower type — the paper's Rule 4, with its
static side condition read on evaluated first-class lists:

```text
Γ ⊢ (λi. branches (S₁ i)) ≡ (λi. branches (S₂ i))
labels (S₁ i) ⇓ Φ₁    labels (S₂ i) ⇓ Φ₂    Φ₁ ⊆ Φ₂
────────────────────────────────────────────────────
Γ ⊢ μˢ S₁ i ⊑ μˢ S₂ i
```

`Φ₁ ⊆ Φ₂` is a meta-level spine check up to conversion, never a reference
to the library `Subset` type; the internal `Subset`/`decide-subset` of
`progress/2.pom` mirror it for programming and proving, and must agree
with it on closed lists. The branch premise is global in `i` so the
carriers agree. Widening does not change the term,
the resolved ambient tag, or the runtime representation. Branch
descriptions are invariant: structural subtyping between different
payloads is a separate feature requiring explicit variance and coercion
rules, and must not be obtained accidentally from label inclusion.
Signatures whose label sets differ by a live label are not definitionally
convertible — `µ(List A)` never checks as `µ(NonEmpty A)` even under the
default `≡βηφ` conversion (Conversionφ), since both labels are inhabited
at every instance; Eq-φ prunes only demonstrably dead labels, and only
directional `⊑` relates live widenings. If a list or branch function is stuck, use
a postponed constraint or restructure the program; the rule is simply
inapplicable — do not guess inclusion.

### Checker migration

- [ ] Separate conversion/equality from directional subtyping. The present
  `equalTerms` special case for `Constr` mixes both and can report a row
  error while returning base-type equality. Conversion compares pairs and
  lists by their ordinary computation; `Subset` proofs belong only to
  directional `⊑`.
- [ ] Replace `matchConstructors` and `matchConstructorOptionalType` with
  `Label` resolution plus the `c ∈ Φ` spine check on the evaluated
  enabled list. `Local` string equality must not remain the core identity
  test: checked identity is the ambient position.
- [ ] Replace `checkAgainstTypeConstructors` with Sig-in elaboration:
  resolve the label, check `c ∈ Φ` on the evaluated enabled list, and
  check the payload against `⟦branches (S i) c⟧ (Carrier S)`.
- [ ] Split `checkTypeClauses` into widening (Sig-sub) and coverage
  (Sig-case's `Φ ⊆ Ψ` spine check on the evaluated enabled list).
  Coverage must diagnose missing, duplicate, and foreign labels once; a
  stuck check rejects with a diagnostic rather than guessing.
- [ ] Replace `constrSubtType` with checking `in 'c payload` against
  `μˢ S i` per Sig-in; the elaborated term stores the resolved ambient
  position in the term itself (`in (c, payload)`) — no side table and no
  annotated node.
- [ ] Replace `removeTypeConstructors` with Sig-forget subsumption: the
  refinement is forgotten by re-typing, never by rewriting the value or
  erasing the ambient family.
- [ ] Extend normalization and conversion through `IData`, pairs and
  projections, `Label`/`At`, list computation, `πₖ`/`switchₖ`, and the
  Sig-case reduct, while keeping `μᴵ`/`μˢ` opaque except for their stated
  computation. Normalize a resolved branch enough to expose its
  description, with explicit cycle/stuck behavior.
- [ ] Implement uniform surface `Mu` elaboration to `μˢ` and its
  `μˢ S i ⊑ Carrier S i` subsumption. Do not infer fixed-point covariance
  from signature inclusion or add a carrier-to-signature downcast without
  `coverFull` evidence.
- [ ] Add a later elaboration phase for current `Static` constructors and
  `{T :: |...}` syntax. `purefyPTerm` currently lowers rows before
  definition metadata is available, which is too early to resolve
  canonical ambient tags.

### Acceptance evidence

- [ ] The future compiler accepts the `progress/2.pom` signature algebra
  directly over `Sig I E` pairs and label-list proofs, without legacy
  `Constr` rows, user-postulated `Static` bridge tokens, or any wrapper
  universe.
- [ ] `{T :: Φ}` elaborates by synthesizing `T`'s ambient enum and
  checking `Φ : List (Label E)`; the legacy `'σ Ee T` spelling elaborates
  through the same pair. Closed lists decide membership, subset,
  disjointness, and coverage by computation; an open list remains a
  neutral term with usable proofs rather than receiving guessed metadata.
- [ ] A smaller signature subtypes a larger one over the same branch
  family via the evaluated-list inclusion side condition; the internal
  `Subset` theorems mirror it. The reverse direction fails.
- [ ] Signatures with different enabled label sets are not definitionally
  convertible: `µ(List A)` cannot check as `µ(NonEmpty A)` through
  Conversionφ, even though both share one `Full` carrier — the default
  `≡βηφ` prunes only demonstrably dead labels, and both labels here are
  live.
- [ ] One full `switch E_ambient` branch function type-checks unchanged
  inside both the full and the restricted signature.
- [ ] Alpha-renamed binders, beta-redex branch functions, eta-expanded
  functions, and computed `switch` branches compare successfully.
- [ ] A singleton enabled list `['new]` inherits the ambient positions
  `{empty ↦ 0, new ↦ 1}`; introduction stores position `1+0`, never a
  standalone singleton position `0` or the ambient `empty` position.
- [ ] Checked introductions carry their resolved ambient position in the
  term;
  identical printed labels from different ambient enums are distinct
  `Label` types and cannot reduce against one another.
- [ ] The same label with a different payload or result-index description
  is rejected.
- [ ] Wrong-family constructors, foreign labels, duplicate match clauses,
  and incomplete coverage are rejected with focused diagnostics; repeated
  enabled labels have set semantics.
- [ ] `union` over closed signatures normalizes to label-list union, while
  `disjoin` rejects overlap. The same operations on open signatures retain
  their list recursion and explicit subset/disjointness evidence instead
  of consulting or inventing a host set.
- [ ] Surface `µ (NonEmpty A)` elaborates to the Unit-indexed `μˢ` and
  admits a `new` node whose recursive tail is the full-carrier `empty`,
  demonstrating ambient recursion and head-only refinement.
- [ ] `prependNE : A → Mu (List A) → Mu (NonEmpty A)` checks by Sig-in on
  the enabled `new` tag, with the recursive tail accepted at the carrier
  by subsumption alone. `headNE : Mu (NonEmpty A) → A` needs one clause;
  the raw tail projection returns the ambient carrier, while a surface
  `tailNE : Mu (NonEmpty A) → Mu (List A)` additionally performs
  `coverFull` reconstruction.
- [ ] Reject an alleged total conversion `Mu (List A) → Mu (NonEmpty A)`
  unless it handles `empty` through an optional result, receives a fresh
  `A`, or successfully matches the outer tag as `new`.
- [ ] Indexed examples compare the instantiated `T c` descriptions after
  substitution and conversion.

References: Figures 1–4 of
`~/Workspace/Subtyping-Theory/first-class-inductive-types.pdf`; Rules 1–4,
6–7, and optional `βηφ` conversion in
`~/Workspace/Subtyping-Theory/subindex/LIPIcs_2021_Version_Sample/subtyping_paper.tex`.
