# Proposal revision changelog

Revision of `progress/type-rules.md`, `context.md`, `progress/1.pom`,
`progress/2.pom` (2026-08-23). Source of truth: EID Figures 1–4 and the
constructor-subtyping paper, Rules 1–7.

## Type-theory holes found and fixed (critical)

1. **Universe violation in `SameAmbient`.** It was declared
   `: … → Set₀` while storing an equation between `Set₁` functions
   (`Branches S = Branches R : EnumT E → IDesc I`), which is predicatively
   impossible. Fixed by eliminating the relation: ambient agreement is now
   judgmental (`≡`), as in the paper's Rule 4 side condition
   `(T Δ*)βη = (T' Δ*)βη`.
2. **Untyped label in `MuSig-in`.** The rule used `c` with no formation
   premise. Fixed: Sig-in carries `Γ ⊢ c : Label E`.
3. **Nondeterministic case reduction.** `MuSig-case` allowed duplicate
   clause labels, making the reduct ambiguous. Fixed: Sig-case requires
   pairwise-distinct clause tags, and the label/tag bijection
   (`Label E ≅ EnumT E`, from uniqueness of `At` proofs) is stated, making
   the selected branch unique.
4. **Ill-founded `iinduction` beta law.** `hyps` was used with missing
   arguments and no type. Fixed: `hyps` is given its full type and
   equations, and the law now reads
   `iinduction R P step i (in xs) ↦ step i xs (hyps (R i) (μᴵ R) P (iinduction R P step) xs)`.
5. **`switch` equations pattern-matched on tuples `π` never defined.**
   Added the missing `πₖ` computation rules
   (`πₖ nilE P ↦ 1`, `πₖ (consE t E) P ↦ P 0 × πₖ E (P ∘ 1+)`), without
   which `switchₖ`'s stated equations are not well formed.
6. **Coercion coherence was load-bearing but unproved.** The coercive
   `<: ⇝ c` design required `weaken refl ≡ id`, transitivity coherence,
   and `eraseˢ`-commutation as axioms-in-waiting; any failure would break
   subject reduction. Fixed structurally: subtyping is now coercion-free
   (the paper's actual discipline — signatures are phantom refinements),
   so every coherence law is trivially `t = t` and the hole cannot exist.

## Simplifications

1. **Signatures are ordinary pairs.**
   `Sig I E := (EnumT E → IDesc I) × List (Label E)`, written `{T :: Φ}`
   as in the subtyping paper. This deletes the primitive
   inductive-recursive `ISig`/`AmbientEnum` block and its admissibility
   obligation; EID Figure 1's pairs already provide the type.
2. **Judgmental fusion deleted.** `branches {T :: Φ} ≡ T` and
   `labels {T :: Φ} ≡ Φ` are pair-projection computation (EID Fig. 1b),
   so the special `signature_from_list` fusion primitives — needed only to
   type the cons clause on a neutral tail — are no longer primitives at
   all; `signature_from_list T Φ := {T :: Φ}` and its fold equations hold
   definitionally.
3. **`SameAmbient`/`transportLabel` machinery deleted.** With the ambient
   enum as a type index (`Sig I E`, `Label E`), both operands of every
   relation share `E` syntactically; the dependent-pair
   `unionSigWithAmbient` contortion and all transports disappear.
4. **One algebra level instead of two.** The former §8 (ISig-level union
   with transports) and §13 (list-level algebra) duplicated each other;
   the revision keeps only the list level, which is what `2.pom` uses.
5. **`Enabled` inductive deleted.** Enabled membership is list `Member`,
   already defined in `2.pom`; introduction/elimination/widening consume
   `Member`/`Subset` proofs directly.
6. **Coercions deleted.** `⇝ c`, `eraseˢ`, `weaken`, `transportPayload`,
   and the annotated node `inˢ⟨S;i;c;a;m⟩` are gone. Introduction is EID's
   `in (tag c, xs)` with `Member` as a checked (not stored) premise;
   Rule 2/Rule 4 analogs re-type the same term. `2.pom`'s `weaken_value`
   is now literally the identity.
7. **`σᴰ`/`'σ` split deleted.** Signatures are no longer descriptions, so
   EID's `'σ` keeps its one meaning and no internal duplicate is needed.
8. **`Covers` unified with `Subset`.** Case coverage is
   `Subset (labels (S i)) Ψ` — the same relation Rule 4 uses, mirroring
   how the paper reuses `⊆` in Rules 4 and 7.
9. **`FullSelection` unified with `Subset`.** Full-coverage downcasting is
   `coverFull : Subset (allLabels E) (labels (S i)) → …`.
10. **κ/Φ cache discussion compressed to one subsection.** With signatures
    as pairs of computing data, "closed fast path" = "closed terms
    evaluate"; `κ` is only a name-resolution table. The multi-page cache
    semantics (three sections) reduced to elaboration notes with the same
    invariants (caches agree with computation; no evidence about neutral
    terms).
11. **Special judgment forms dropped.** `Γ ⊢ c : Label E` and
    `Γ ⊢ p : Subset …` are ordinary typing; the judgment list is now
    ⇒/⇐/≡/⊑ only, matching the papers' `Γ ⊢ t : A` and `Γ ⊢ A ⊑ B`.

## Renamings

- `ISig I` → `Sig I E` — it is no longer an `IDesc`-like universe, and the
  ambient enum belongs in the type (EID style: `EnumT E`, `IDesc I`).
- `<: ⇝ c` → `⊑` — the paper's coercion-free relation and symbol.
- `sig∅[E,T]` → `{T}` / `{T :: []}` — the paper's brace notation.
- `MemberList`/`SubsetList`/`DisjointList` → `Member`/`Subset`/`Disjoint`
  — one name per relation, taken from `2.pom`; the type-rules and goal
  program previously disagreed.
- `Enabled S c` → `Member c (labels S)` — see Simplification 5.
- `inᴵ`/`inˢ` → `in` — one introduction form, as in EID.
- `DescChoice`/`IChoice` naming and rule labels normalized to
  `Sig-mu`, `Sig-in`, `Sig-forget`, `Sig-sub`, `Pi-sub`, `Sig-case`, each
  tagged with its paper rule number.

## Syntax improvements

- `{T :: Φ}` adopted as the signature spelling — identical in shape to the
  subtyping paper's `{T Δ* :: Φ}` and to PomPom's existing `{T :: |c}`
  row syntax, while `\append`/`{T}` remain as derived forms so `2.pom`'s
  fold reading is unchanged.
- `signature_from_list` argument order unified to `T` then labels with
  `{E}` implicit (`type-rules.md` previously wrote `E T cs` while
  `context.md`/`2.pom` wrote `T cs`).
- `2.pom` reordered so the label-list algebra precedes its uses (no
  forward references), and `weaken_value` gained its one-line body.
- `1.pom` terms simplified by phantom subtyping:
  `oneThenEmpty = in 'new (1, in 'empty unit)` (no `eraseˢ` wrapper), and
  signature annotations name their ambient enum (`Sig () ListE`).

## Second pass (2026-08-23, after review of `2.pom`)

1. **`signature_from_list` deleted everywhere.** It was a vacuous lift —
   `signature_from_list T Φ = {T :: Φ}` mixed the list level with the
   signature level while doing no work. Formation is the pair itself, and
   the operations are now genuinely signature-level: `union-sig` and
   `disjoin-sig` consume and produce `Sig` values through the projections,
   while deciding happens at the constructor level.
2. **Core labels are ambient positions: `Label E := EnumT E`.** The
   subtyping paper needs only decidable constructor identity, so the
   name-carrying Σ package was elaboration data in disguise; `At`/names
   moved to the elaboration section. This deletes `tag`, and spares the
   At-uniqueness and dependent-pair-equality lemmas that deciding equality
   of packaged labels would have required — `decide-label` is now a
   complete Nat-style induction.
3. **`2.pom` rewritten in PomPom-usual syntax**, structured as the stated
   goal pipeline — decide constructors, then constructor lists, then
   signatures: `Static`/`|args :: telescope => body.` definitions, match
   brackets, `def` locals, and `libs/` vocabulary (`Or`, `AxB`, `False`,
   `⊥`, `Eq`, `rewrite`, `cong`, `List`); no `forall`, `data`, `let`,
   `case of`, or `by decide`.
4. **The decision pipeline is programmed, not postulated.** `decide-label`
   (with inline `eq_rect` no-confusion), `decide-member`, `decide-subset`,
   `decide-disjoint`, `subset-concat-left/right`, and the `union`/`disjoin`
   theorems all have complete bodies; closed facts are extracted by the
   dependent-match `from-dec` (`FromDec` motive computes to `P` on a `yes`),
   replacing the pseudo `by decide`/`by reflexivity`.
5. **Set union, `NoDup`, and `Overlap` dropped from the goal program** —
   refinement consults a list only through `Member`, so duplicates already
   have set semantics and canonical de-duplication is routine with
   `decide-member`; noted as a remark instead of carried as code.

## Third pass (2026-08-23, layering of `Member`/`Subset`)

1. **Core side conditions are meta-level again — the thin separation is
   removed.** The proof-premise formulation (`Γ ⊢ p : Subset …` inside
   Sig-in/Sig-sub/Sig-case) made core rules name library-defined types,
   inverting the layering (the calculus would depend on user space). The
   rules now state the paper's own side conditions — `C ∈ Φ`, `Φ' ⊆ Φ`,
   coverage — directly: evaluate the first-class label list to its spine
   (`labels (S i) ⇓ Φ`), then check membership/inclusion syntactically up
   to conversion. The core never mentions `Member` or `Subset`.
2. **`Member`/`Subset`/`decide-*` are the internal mirror, not core
   input.** They remain ordinary library definitions used to state and
   prove the quantified algebra (`union`, `disjoin`, `UnionInto`).
   Agreement with the core checks on closed lists — `decide-*` returns
   `yes` iff the spine check succeeds — is a stated §10 obligation.
3. **Stuck means stuck.** A side condition that cannot be established on a
   neutral list makes the rule inapplicable and the program rejected with
   a diagnostic; it is never read as negative evidence, and no rule
   accepts an open value-level use on the strength of a library proof.
   Open signature work stays at the proof level — which is all the
   future-work examples require, since their value-level uses
   (`forget-nonempty`, the List/NonEmpty instance) are closed.
4. `coverFull` restated per instance (definable when the evaluated enabled
   spine contains every ambient position) instead of taking a library
   `Subset` argument, for the same layering reason.

## Coverage check (examples remain derivable)

- `1.pom`: `ListE`/`ListBranches` are EID Fig. 2/4 terms plus `switchₖ`;
  `List`/`NonEmpty` are `{T :: Φ}` pairs (Sig-mu formation); `prependNE`,
  `singletonNE`, `oneThenEmpty` check by Sig-in with closed `Member`,
  tails accepted at the carrier by Sig-forget + Subsumption; `headNE`
  checks by Sig-case with decided coverage `Subset ['new] ['new]`;
  `µ(NonEmpty A) ⊑ µ(List A)` by Sig-sub with decided
  `Subset ['new] ['empty,'new]`, and the converse remains underivable
  (no rule shrinks a label set).
- `2.pom`: `Dec`, `Label`, `Member`, `Subset`, `Disjoint` are ordinary
  PomPom definitions; `decide-label` is complete position induction with
  inline `eq_rect` no-confusion; `decide-member`/`decide-subset`/
  `decide-disjoint` recurse over it with `Or` and `rewrite` plumbing from
  `libs/`; `union-sig`/`disjoin-sig` are pairings through the projections
  and `union`/`disjoin` are `MkPair`s of the concat inclusion lemmas. In
  the closed instance, `from-dec` extracts `empty-new-disjoint` and
  `nonempty-is-list` because the decisions compute to `yes`,
  `union-is-list-sig` closes by `refl` since `concat` evaluates, and
  `forget-nonempty` is the identity checked by Sig-sub + Subsumption.

## Conversionφ adopted as default (2026-08-26)

1. The subtyping paper's optional `φ` layer (`Norm-φ`, `Eq-φ`,
   `Conversionφ`; TeX lines 469–507) is now the **default**: conversion is
   `≡βηφ` and the checking rule is Conversionφ.  Because a signature is a
   pair term whose projections must keep computing, Eq-φ is stated on the
   refinement types `μˢ S i`, never on the pairs: two refinements of one
   branch family are definitionally equal when their evaluated enabled
   spines prune to a common spine at the instance (type-rules §1, §7).
2. The `AGAINST` analog is a conservative, positively-derived emptiness
   judgment on evaluated payload descriptions: a `'σ` over an enumeration
   spine evaluating to `nilE` (the paper's head-constructor clash),
   propagated through `'×` and through every branch of an exposed choice;
   `'var`, `'1`, `'Π`, `'Σ` never prune.  A stuck description or index
   never prunes — stuckness is still never evidence.
3. Consequences: `µ` types differing only by demonstrably dead labels are
   definitionally equal (the paper's `{Vector A (S n) :: |empty|cons}`
   example); List/NonEmpty stay non-convertible because both labels are
   live.  Sig-case keeps `Φ ⊆ Ψ` coverage — the paper's `Ψ = Φok` choice
   is admissible through conversion.  New §10 obligation: soundness of the
   `AGAINST` analog (derived pruning implies an uninhabited payload),
   making Eq-φ type-preserving.
4. Stated formally in `progress/TypeRules.v`: the φ layer (`neutral`,
   `desc_against`, `spine_phi`) precedes conversion, `cv_phi` embeds Eq-φ,
   and the Conv rule's comment carries the paper's Conversionφ ASCII.

## TypeRules.v: declarative completion after a preservation counterexample (2026-08-26)

A kernel-checked counterexample refuted the stated preservation conjecture
in the first Rocq rendition: `πₖ (consE 'c nilE) (λ_. 1)` is well typed and
steps to a Σ whose domain `(λ_. 1) 0` had NO typing derivation — the
bidirectional rendition made application, projection, and the Sig-case
scrutinee synthesis-only, while unannotated λ (and pairs, and `in`) only
check.  The sketch's declarative rules were never affected; the hole was
the rendition's.  Fix, in `progress/TypeRules.v`:

1. `check` gains the declarative eliminator rules App-check, Fst-check,
   Snd-check — EID Fig. 1's application/projection typing read
   declaratively, with the eliminated type chosen existentially and its
   formation premise explicit (the sketch's suppressed-well-formedness
   policy).
2. Sig-case's scrutinee premise is now `Γ ⊢ M ⇐ μˢ S i`, matching the
   paper's plain `Γ ⊢ M : {T Δ* :: Φ}` — a literal `case (in …) of …`
   redex is typeable, as the paper's ξ-case' subject-reduction argument
   requires.
3. The counterexample is smoke-checked closed: the πₖ reduct, λ-motive
   applications and all, now has a full checking derivation.

## TypeRules.v: against_sound scoped to well-typed descriptions (2026-08-26)

Second kernel-checked counterexample: `against_sound` was stated untyped.
`desc_against` reads reduction behaviour, and on ill-typed terms step is
not confluent — st_case does not require distinct labels (distinctness is
Sig-case's TYPING premise), so the ill-typed
`case (in (0, unit)) of 1 { 0 ⇒ 'σ nilE '1 ; 0 ⇒ '1 }` reduces both to a
dead choice (giving `desc_against`) and to `'1` (giving an inhabitant of
its interpretation), refuting the conjecture.  Fix: `against_sound` now
carries the ⟦_⟧ formation premises (index type, description, carrier
family well-typed) — φ only needs soundness for well-typed payloads, since
sph_drop prunes descriptions that reach it through Sig-typed premises.
The ambiguous case is untypeable (its duplicate labels fail Sig-case
distinctness), which is smoke-checked by a derivation-induction proof.

## Raw case reduction is first-match (2026-08-26)

Third kernel-checked counterexample, fatal to the whole conjecture bundle:
with clause selection free, the ill-typed
`fork t u := case (in (0, unit)) of { 0 ⇒ t ; 0 ⇒ u }` stepped to BOTH t
and u, so the untyped conversion collapsed — `conv t u` for all closed t
and u — refuting consistency, consistency_enum, progress, normalization,
canonical_forms_sig, consistency_empty_sig, and the strengthened
against_sound at once.  No statement-level fix exists: the collapse lives
in the conversion the typing rules consume.  Of the two rule-level
repairs, determinizing raw ι-reduction is the standard one (kernel match
reduction is always deterministic on raw terms; the alternative — typed
cv_step — would force conversion into the typing block).  Fix, in both
`type-rules.md` §7 and `TypeRules.v` st_case: the FIRST clause whose label
is canonically the scrutinee's position is selected, and the redex fires
only once every earlier clause label is canonical with a distinct
position.  Canonical positions are step-normal, so the selection is stable
under further reduction; on Sig-case-typed matches (pairwise-distinct
labels) the first match is the unique match, so the typed fragment is
unchanged.  Smoke: the fork's second reduction is now formally
underivable (`~ step ambiguous '1`), while the first-clause reduction,
desc_against, and untypeability of the duplicate-label case still check.

## TypeRules.v: 1+ evaluates its argument (2026-08-26)

Fourth kernel-checked counterexample: progress and normalization were
refutable through a stuck well-typed case.  The tag `1+ ((λ_. 0) unit)`
is well typed (App-check), and Sig-in/Sig-case accept it — the `c ∈ Φ`
side condition is up to conversion, needing no canonicity — but `enum_pos`
reads position spines syntactically and `step` had no congruence for the
argument of `1+`, so the tag could never become canonical: the case was
neither a value nor reducible.  Fix: `st_esucc1` — `1+` evaluates its
argument, the exact analogue of the pair-component congruences.  The
first-match determinism argument survives: a canonical position's argument
is canonical, so canonical positions remain step-normal and clause
selection stays stable (smoke-checked as pos_step_normal), and the
formerly stuck case now runs to a value (smoke-checked end to end).

## TypeRules.v: canonical_forms_sig gains the index premise (2026-08-26)

Fifth kernel-checked counterexample: canonical_forms_sig stated every
formation premise of the refinement type except the index's.  Eta makes
`conv (λx. 0 x) 0` a raw fact, so ch_expand re-types a valid node
`M : μˢ Sf 0` at `μˢ Sf (λx. 0 x)` — and a signature that switches on its
index is permanently stuck at the ill-typed index (a λ is step-normal and
no switch rule fires on it), so its enabled list never exposes a spine and
the promised spine_mem is impossible.  Fix: the statement now carries
`Γ ⊢ i ⇐ I` alongside the other formation premises — completing the
sketch's suppressed-well-formedness policy for the μˢ type's data.  No
type or evaluation rule changed.

## Progress proved relative to a named interface (2026-08-27)

`progress/Progress.v` proves the progress conjecture's exact statement
(`progress_proved`, ~990 lines, no Ltac automation beyond bullet
discipline) by size-measure induction, mutually with a position-progress
lemma for `1+` spines.  The development derives what was previously
hand-waved: a weak-head classification with λ deliberately unclassified
(eta makes it head-promiscuous), subtyping transport showing pure-conv
chains preserve the target type while proper subtyping lands only in the
sort/Π/μˢ classes plus the Sig-forget flip; canonical forms for checked
values (synthesis is syntax-directed, so only ch_expand recurses); typing
inversion for all ten eliminator shapes; and the case redex fired through
canonical forms at μˢ, spine/coverage transport, and a first-match witness
with the prefix condition st_case demands.  Notably: values of Π type are
exactly λ/μᴵ/μˢ; switch over an evaluated-nil enum is impossible by EnumT
injectivity; a stuck μ application classifies only as a sort.

Print Assumptions certifies the theorem stands on exactly six axioms: the
five confluence-grade conversion facts stated as the file's interface
(conv_whd — conversion cannot cross weak-head classes; conv_enumt_inj;
conv_pos; spine_covered; muapp_sort) and canonical_forms_sig (TypeRules
§8).  These are the §10 conversion metatheory, now isolated as the entire
remaining gap for progress.  Normalization is NOT addressed — it needs
termination on top of this skeleton.
