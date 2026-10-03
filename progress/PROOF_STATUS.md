# Proof status

**Annotation repair in progress (September 30):** the user selected explicit
core annotations with general eta contraction. The new
[annotated development](annotated/README.md) has checked typing, binding,
weakening, substitution, beta preservation, and counterexample regressions.
Full annotated preservation and the public migration remain unfinished.
The counts below continue to refer to the existing named calculus.

Of the 47 original claims, **46 are proved without axioms and one is
refuted**. Progress, operational preservation, and full beta/eta strong
normalization are proved. Coercion coherence and checking coherence are proved
with their original statements through a binary relational model; see
[RELATIONAL_PLAN.md](RELATIONAL_PLAN.md). No conjectures remain.

`full_preservation` is false under the current rules, including function
cumulativity. [OpenSignaturesEtaPolymorphism.v](OpenSignaturesEtaPolymorphism.v)
proves its negation without axioms. The exact original proposition is retained
as `full_preservation_statement`; its false axiom declaration was removed and
[archived](../proof-archive/2026-09-28-before-polymorphic-eta-refutation/README.md).
The other 46 original statements and all calculus rules are unchanged by this
refutation. The requested 47/47 proof target requires a specification repair;
it cannot be reached by proof automation under these rules.

## Progress, preservation, and normalization

| Claim | Checked result | Remaining assumptions |
| --- | --- | --- |
| `progress` | Induction over every typing rule, with canonical forms and proved conversion joinability. | None |
| `preservation` | Every root computation and evaluation context, transported through typed encoding/reflection. | None |
| `preservation_eval` | Induction over evaluation using proved operational preservation. | None |
| `normalization` | Full semantic fundamental theorem, inhabited semantic environments, substitution reflection, and named encoding. | None |
| `normalization_eval` (supporting theorem) | Strong normalization supplies enough evaluator fuel; progress identifies the terminal result as a value. | None |
| `confluence` | Parallel beta/computation and eta diamonds, commutation, and an encoding/reflection proof for named terms. | None |
| `consistency` | Normalize a hypothetical bottom inhabitant and exclude bottom values. | None |

Progress, execution preservation, confluence, and conversion joinability have no axiom dependencies. The progress argument
constructs type-formation evidence directly from the typing rules. An
invariant for enum-product and description computations avoids using
preservation to classify their results.

The operational proof does not use full preservation. The general eta premise
of the separate full-preservation argument is now refuted. This does not
invalidate operational preservation or normalization; neither depends on it.

## Closed claims

| Claim | Proof |
| --- | --- |
| `context_validity` | Induction on typing. |
| `weakening`, `substitution`, `type_correctness` | Nameless structural rules, typed encoding, and typed reflection. |
| `abort_typing`, `unroll_typing`, `row_code_typing`, `signature_typing` | Derived rules using the proved weakening theorem. |
| `list_definitions_well_typed`, `nil_typing`, `cons_typing`, `nonempty_cons_typing`, `reused_tree_cons_typing`, `nonempty_widening`, `nonempty_observers_typing` | Symbolic typing proofs using proved structural rules. |
| `conversion_joinability`, `confluence` | Parallel reduction with named/nameless encoding and reflection. |
| `progress` | All typing rules, using closed conversion joinability. |
| `preservation`, `preservation_eval` | Independent root computation proofs, evaluation contexts, and induction over evaluation. |
| `close_induction_preservation` | Payload inversion, typed diagonal motive and recursive calls, and induction-method application. |
| `canonical_forms_close` | Constructor inversion and injectivity of conversion at close types. |
| `dead_sound`, `row_handlers_sound`, `description_subtyping_sound`, `subtyping_sound`, `case_handlers_sound`, `synthesis_sound`, `checking_sound` | Typed computation/eta factorization supplies constructor views without full preservation. |
| `closing_substitution` | Context inclusion, substitution algebra, and independently proved beta preservation. |
| `label_resolution_unique` | Conversion preserves row positions; distinct row names determine a unique position. |
| `conversion_substitution` | Beta expansion, congruence, and beta reduction. |
| `next_step_sound` | Structural induction and evaluator case analysis. |
| `run_sound` | Induction on fuel. |
| `unroll_beta` | Two root steps. |
| `row_position_identity` | Induction on the row and position. |
| `singleton_source_elaborates` | Elaboration constructors and bounded, checked search for concrete typing and conversion goals. |

The conversion-substitution proof avoids a substitution-algebra induction:
`subst s k t` converts backwards to `(lambda k. t) s`, congruence changes
`t` to `u`, and beta reduction gives `subst s k u`.

The local `os_check` and `os_compute` tactics construct ordinary proofs
using core rules, alpha equivalence, and `run_sound`. Their fuel bounds
proof search; it is not evidence of normalization.

## Independent foundations

[OpenSignaturesBinding.v](OpenSignaturesBinding.v) proves substitution
extensionality and identity on free variables, substitution freshness,
alpha invariance of free variables, typing/context scoping, and fresh-ID
existence. It imports no metatheory conjectures.

[OpenSignaturesProgress.v](OpenSignaturesProgress.v) proves rigid-head
invariants for reduction and alpha equivalence, transport of reducibility
under alpha, formation of families and fixed-point applications,
operational-step inclusion in full reduction, evaluator completeness for
step existence, and termination of the evaluator on accessible terms.
Its canonical-form and progress results take joinability as an explicit
premise; the file imports no metatheory conjectures.

[OpenSignaturesSubstitution.v](OpenSignaturesSubstitution.v) proves
substitution compatibility with alpha equivalence, the exact free-variable
support of simultaneous substitution, binder renaming, and substitution
composition up to alpha. All these proofs are axiom-free.

[OpenSignaturesConfluence.v](OpenSignaturesConfluence.v) proves untyped
conversion joinability and confluence modulo alpha. The auxiliary
[nameless](nameless/) development proves parallel beta/computation and eta
diamonds and their commutation. The encoding modules prove alpha equivalence,
substitution, and both directions of reduction correspondence. No typing,
preservation, or normalization conjectures enter these proofs.

[OpenSignaturesLabels.v](OpenSignaturesLabels.v) derives uniqueness of row
label resolution from raw conversion joinability and distinct row names.

The derived typing modules cover ordinary functions and products, description
payloads, row selection and construction, handler tuples, row mapping, and
case analysis. They take weakening explicitly and import no conjectures.
Elaboration soundness is proved by simultaneous induction, with explicit
weakening, dead-witness typing, and coercion typing premises. This avoids
circular use of synthesis and checking soundness.

The earlier concrete helpers `eval_conv`, `list_def_unit`,
`nonempty_def_unit`, and `nil_unit` also have no axiom dependencies.

## Normalization consequences

All six formerly conditional original claims are now closed, including
`consistency` above.

| Claim | Remaining assumptions |
| --- | --- |
| `dead_close_uninhabited` | None |
| `canonical_forms_named`, `self_restricted_list_empty`, `close_roll_unroll`, `no_uniform_list_downcast` | None |

The downcast argument instantiates the alleged function at `Bot`, applies
it to the empty list, and uses the nonempty-list head observer and consistency.

## Computation preservation

[DBRootPreservation.v](nameless/DBRootPreservation.v) proves preservation for
all root computations. Shared constructor inversion handles description
interpretation, `iAll`, `hyps`, enumeration products and switches, reference
induction, close cases, and close induction. No metatheory conjectures are
imported. Its eta result covers a lambda reduct only, not arbitrary functions.

[DBPreservation.v](nameless/DBPreservation.v) lifts these proofs through every
operational context. [OpenSignaturesPreservation.v](OpenSignaturesPreservation.v)
then reflects the result into the named calculus. The public `preservation`,
`preservation_eval`, and `close_induction_preservation` are closed without axioms.
Canonical-form, context-exchange, and coercion proofs now request operational
preservation wherever that suffices, removing unnecessary full-preservation
dependencies from the normalization-based results.

[DBOperatorFormations.v](nameless/DBOperatorFormations.v) uses a shared binder
tactic to form dependent induction types. Bounded conversion and formation
search discharge the annotation and congruence cases in
[DBFullPreservation.v](nameless/DBFullPreservation.v). Its theorem takes general
eta subject reduction as an explicit premise. It does **not** discharge the
original full-preservation claim, and is not counted among closed claims.
Its general eta premise is now known to be false.

The additional [DBCumulativeTyping.v](nameless/DBCumulativeTyping.v) library
lifts checked chains of conversion and universe comparison through dependent
function types, including context narrowing.
[DBTypedPiViews.v](nameless/DBTypedPiViews.v) recovers well-typed function-type
representatives using computation preservation.
[DBTypeComparison.v](nameless/DBTypeComparison.v) proves transitivity,
substitution stability, and realization of raw structural comparisons when
both endpoints are well formed. This also permits strengthening comparison
chains without requiring well-formed intermediate types in the smaller context.
[DBEtaPrincipal.v](nameless/DBEtaPrincipal.v) uses these results to prove eta
preservation for variables at arbitrary dependent function types, and for
functions with a stable principal type. The polymorphic-application
counterexample shows why this premise cannot cover arbitrary functions.
These supporting results do not change the 44/47 proved count. See
[PRESERVATION_PLAN.md](PRESERVATION_PLAN.md) for the remaining argument.

## Typed factorization and normalization foundations

[DBComputationPreservation.v](nameless/DBComputationPreservation.v) proves
preservation for every computation context, including binders and annotations.
[DBParallelPreservation.v](nameless/DBParallelPreservation.v) serializes parallel
computation with one shared congruence tactic and proves its preservation.

[DBEtaSafety.v](nameless/DBEtaSafety.v) proves that typed eliminations cannot
inspect a lambda as a data constructor, and that eta preserves this invariant.
[DBEtaPostponement.v](nameless/DBEtaPostponement.v) proves strong postponement:
one parallel eta step followed by one parallel computation can be replaced
by one parallel computation followed by eta steps. It then factors any full
reduction from a typed term into computation followed by eta.

[DBDescriptionViews.v](nameless/DBDescriptionViews.v) uses this factorization
and constructor inversion to recover typed product and empty-choice views.
The named views reflect these witnesses back through the encoding. This removes
all conjecture dependencies from dead-witness, handler, subtyping, synthesis,
and checking soundness. General eta preservation is separately refuted.

[DBActiveParallel.v](nameless/DBActiveParallel.v) records whether a parallel
step performs a computation and proves that an active step contains a nonempty
computation sequence. [DBActivePostponement.v](nameless/DBActivePostponement.v)
preserves this activity through eta postponement, excluding silent steps from
the termination argument.

[DBNormalization.v](nameless/DBNormalization.v) now proves that computation
termination implies full reduction termination for every typed term. Eta
contractions are handled by term size; computational contractions decrease
accessibility for active parallel steps. General eta preservation is not needed.
[OpenSignaturesNormalization.v](OpenSignaturesNormalization.v) transfers this
result to the named calculus.

[DBComputationSubstitution.v](nameless/DBComputationSubstitution.v) proves that
substitution preserves individual computation steps and reflects normalization.
[DBReducibility.v](nameless/DBReducibility.v) proves reducibility candidates for
dependent functions and pairs, including lambda and pair introduction, function
variance, and semantic eta equivalence. Semantic eta equivalence concerns
computability predicates; it does not prove eta subject reduction for typing. These
are also used by the complete normalization proof below.

The full-reduction semantic model now has these checked components:

- [DBFullReductionStructure.v](nameless/DBFullReductionStructure.v) proves
  preservation of individual beta/eta steps under lift and substitution.
- [DBFullNormalForms.v](nameless/DBFullNormalForms.v) supplies a sound and complete
  step selector, a normalizer given accessibility, and uniqueness of normal forms.
  The normalizer still requires a termination proof.
- [DBFullReducibility.v](nameless/DBFullReducibility.v) proves the function and
  pair candidate laws for full reduction, including eta in lambda introduction.
- [DBSemanticTypes.v](nameless/DBSemanticTypes.v) interprets dependent types over
  an atomic interpretation. Conversion preserves the interpretation, and
  interpretations are unique up to predicate equivalence. Canonical predicates
  let dependent codomains be interpreted without a choice axiom.
- [DBUniverseModel.v](nameless/DBUniverseModel.v) constructs the full numeric
  hierarchy, proves cumulativity and cross-level coherence, and validates
  dependent Pi and Sigma formation. The atomic interpretation is indexed by
  level so description types can remain above the small universe.
- [DBPositiveCandidates.v](nameless/DBPositiveCandidates.v) proves saturation,
  positive fixed-point candidates, and their fold, unfold, and induction laws.

The concrete interpretation is now supplied by additional checked modules:

- [DBIndexedCandidates.v](nameless/DBIndexedCandidates.v) restricts recursive
  references to computable indices and proves fixed-point coherence,
  refinement, and index conversion.
- [DBDescriptionCandidates.v](nameless/DBDescriptionCandidates.v) controls
  original description function fields at every computable argument.
- [DBEnumCandidates.v](nameless/DBEnumCandidates.v) interprets enumeration
  positions, including an empty enumeration using the least candidate.
- [DBDescriptionModel.v](nameless/DBDescriptionModel.v) proves existence,
  uniqueness, candidate validity, and positivity of description meanings.
- [DBSmallTypeModel.v](nameless/DBSmallTypeModel.v) constructs the nested
  positive model of small atomic types, including reference fixed points and
  closure, and proves its coherence by guarded recursion.
- [DBCalculusModel.v](nameless/DBCalculusModel.v) instantiates the cumulative
  hierarchy, with description types starting at level one, and proves
  semantic formation for enumerations, descriptions, fixed points, and closure.
- [DBSemanticGeneration.v](nameless/DBSemanticGeneration.v) gives semantic
  inversion for universes, functions, and pairs. Original substituted
  codomains retain an explicit normalization premise.

The semantic operator proofs now cover `Interp`, `IAll`, `Hyps`, `EPi`,
`Switch`, `CloseCase`, `Ind`, and `CloseInd`. The induction proofs refine the
positive fixed-point candidates with computability of recursive calls; the
`Hyps` proof uses those refinements only at the children selected by the
description. `CloseInd` handles independent reduction of its repeated
reference definition and an arbitrary outer signature. Enumeration codes
retain computable tails in their candidate interpretation.

The shared proofs are in `DBHeadExpansion.v`, `DBBetaExpansion.v`,
`DBSaturatedElimination.v`, and `DBEliminatorCandidates.v`. The operator
modules end in `Computability.v`; all are included in the assumption audit.
[DBSemanticBinders.v](nameless/DBSemanticBinders.v) also exposes candidate
and stability laws of normalized codomains. [DBSemanticJudgments.v](nameless/DBSemanticJudgments.v)
uses them to validate the semantic rules for dependent functions, pairs,
universes, variables, conversion, and sort cumulativity.
[DBSemanticVariance.v](nameless/DBSemanticVariance.v) validates function
cumulativity by induction on a comparison-depth bound preserved by substitution
and reduction. [DBSemanticSubstitution.v](nameless/DBSemanticSubstitution.v)
now supplies simultaneous substitution, semantic environment extension,
full-step preservation, and normalization reflection.

[DBSemanticFamilies.v](nameless/DBSemanticFamilies.v),
[DBSemanticData.v](nameless/DBSemanticData.v), and
[DBSemanticCloseMethods.v](nameless/DBSemanticCloseMethods.v) interpret the
derived family, definition, motive, and induction-method types.
[DBSemanticOperators.v](nameless/DBSemanticOperators.v),
[DBSemanticPrimitiveRules.v](nameless/DBSemanticPrimitiveRules.v), and
[DBSemanticCloseCase.v](nameless/DBSemanticCloseCase.v) validate all remaining
typing rules. [DBSemanticFundamental.v](nameless/DBSemanticFundamental.v)
proves the fundamental theorem for every typing derivation, inhabits semantic
environments, and reflects full-reduction accessibility. The named bridge
proves the original `normalization` statement without assumptions.

These models add no axioms. The original-claim count is **44/47** without
assumptions; see [NORMALIZATION_PLAN.md](NORMALIZATION_PLAN.md) for the proof map.

## Function-cumulativity repair

The previous calculus allowed `lambda x. f x : Unit -> Sort 1` while
`f : Unit -> Sort 0` could not receive that larger function type. Eta
contraction therefore violated preservation. A second case requires domain
contravariance: `f : Sort 1 -> Sort 0` can be applied to `x : Sort 0`, so
its eta expansion has type `Sort 0 -> Sort 0`.

The new `universe_le` relation has reflexivity, universe inclusion `j <= k`,
and recursive Pi variance: domains are contravariant and codomains covariant.
`ty_cumul_fun` changes a function from `Pi x:A. B` to `Pi x:C. D` when
`universe_le C A` and `universe_le B D`. Both function types must be
well formed. Conversion stays separate; distinct universes are not identified.
The rule is implemented in both named and auxiliary nameless typing.

[OpenSignaturesEtaRegression.v](OpenSignaturesEtaRegression.v) proves that
both eta reducts now keep the claimed type, and checks that universes
remain distinct. These are axiom-free regressions, not a general eta or
full-preservation theorem.
The [pre-repair snapshot](../proof-archive/2026-09-27-before-function-cumulativity/README.md)
preserves the old rules and their checked counterexample.

The auxiliary [beta/projection preservation proofs](nameless/DBBeta.v),
[context conversion and narrowing proofs](nameless/DBContexts.v), and
[typed encoding/reflection](OpenSignaturesTypingEncoding.v) cover the new rule.
[OpenSignaturesBeta.v](OpenSignaturesBeta.v) transports beta preservation to
the named calculus. [OpenSignaturesPayloadInversion.v](OpenSignaturesPayloadInversion.v)
recovers a close constructor's typed payload using injectivity of conversion.
These independent results close `closing_substitution` and `canonical_forms_close`.

## Observational-equivalence foundations

[OpenSignaturesObservations.v](OpenSignaturesObservations.v) contains the
unchanged closing-substitution and contextual-observation definitions and
their proved foundations. It imports no public conjecture declarations.
The original `closing_substitution` theorem remains in the public theorem
file and applies the independent named proof.
[OpenSignaturesObservationalLaws.v](OpenSignaturesObservationalLaws.v) proves
reflexivity, symmetry, transitivity, a characterization by closed observation
functions, and congruence under typed closed functions and typed contexts
with a fixed closed result type.
[OpenSignaturesObservationalTypes.v](OpenSignaturesObservationalTypes.v)
proves type-conversion invariance and application congruence. These are
foundations for coherence.
[OpenSignaturesRowCoherence.v](OpenSignaturesRowCoherence.v) also proves that
inhabited closed payloads select live handlers, gives a canonical row-payload
form, and proves conversion of row-map outputs for any two handler derivations
using the same source and target row views.
[OpenSignaturesRowViews.v](OpenSignaturesRowViews.v) transports positions and
branch descriptions between convertible row views.
[OpenSignaturesDescriptionCoherence.v](OpenSignaturesDescriptionCoherence.v)
then proves conversion of any two description-coercion outputs on every closed
typed input, covering identity, dead, and row coercions with differing row
views. These pointwise results do not give contextual equivalence by
themselves.

The original `coercion_coherence` and `checking_coherence` are proved in
[OpenSignaturesTheorems.v](OpenSignaturesTheorems.v) from the binary relational
model in `OpenSignaturesRel*.v`. The model relates closed terms by a
conversion-closed PER at structurally related types, over a cumulative universe
tower with descriptions, least fixed points and close types. Its fundamental
lemma covers all typing rules, and adequacy turns relatedness into
`observational_eq`. Coercions are compared through semantic coercion graphs
that retag sum rows by name; composition of graphs eliminates transitivity
semantically. Elaborations are compared over contexts linked by related types,
which covers case branches whose payload types differ syntactically. Every new
file is closed under the global context. See
[RELATIONAL_PLAN.md](RELATIONAL_PLAN.md).

## Remaining work

No conjecture declarations remain. Full preservation is refuted, not counted
as proved.
No new axioms or weakened theorem premises have been used to discharge claims.
A choice of repaired specification is still needed. The concrete theorem
`named_computation_preservation` in
[OpenSignaturesComputationPreservation.v](OpenSignaturesComputationPreservation.v)
covers all computation contexts, including binders and annotations. It is a
separate checked alternative, not counted as proving the refuted original
beta/eta claim.

[OpenSignaturesTypingEncoding.v](OpenSignaturesTypingEncoding.v) proves
weakening, substitution, and type correctness for the original named calculus.
Its auxiliary nameless typing judgment records result-type formation explicitly.
Both translation directions are proved, including binder freshness, dependent
application, and all generic operators. The auxiliary structural proofs and the
three public theorems have no axiom dependencies.

The archived revised parallel-reduction development has been completed and
adapted through a checked encoding. Archived normalization remains a conjecture.

The original unfinished attempts remain preserved verbatim in
[OpenSignaturesTheorems.partial.v](../proof-archive/2026-09-26/OpenSignaturesTheorems.partial.v).

## Verification

```sh
make -C progress open-signatures check-bindings check-eta-cumulativity check-eta-polymorphism audit-open-signatures
rocq check -silent -Q progress '' OpenSignaturesTheorems OpenSignaturesEtaRegression OpenSignaturesEtaPolymorphism
```

The audit covers the 46 proved claims, the refutation of the remaining
original proposition, and supporting results.
A successful build does not eliminate printed assumptions. Section theorems
such as `progress_from_conversion` close over their explicit joinability
premise; the public `progress` theorem supplies the proved joinability theorem.

The audit binds all 247 closed proof/definition references at their original
points of name resolution, then checks the combined dependency graph once.
Later module imports cannot silently change which constant is audited. The
collection must print `Closed under the global context`; the two coherence
theorems are also printed separately and print the same. This retains all previous coverage while
reducing the measured audit compilation from about 364 seconds to 6 seconds.
