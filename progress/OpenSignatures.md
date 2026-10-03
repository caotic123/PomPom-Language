# Open-signature Rocq specification

This is the relational Rocq version of [type-rules.md](type-rules.md).
The representation uses [stable numeric IDs](STABLE_IDS.md) and an
alpha-equivalence setoid, with sequential term interning and no hashing.
**Forty-six metatheory claims have closed proofs**, including coercion and
checking coherence, and full preservation is refuted. No conjectures remain. See
[PROOF_STATUS.md](PROOF_STATUS.md) for dependencies and
[PROOF_START.md](PROOF_START.md) for the first proof and acceptance check.

The mathematical rule reference, including the repaired function-cumulativity
rule, examples, and paper citations, is available as
[LaTeX](../docs/type-rules/open-signatures.tex) and
[PDF](../docs/type-rules/open-signatures.pdf).
Its named-binder and function-cumulativity rules follow the active source,
which also includes explicit alpha conversion and alpha transport of typing.

```sh
make -C progress check-bindings
make -C progress open-signatures
make -C progress audit-open-signatures
```

The syntax, alpha setoid, core rules, elaboration, examples, and binding
regressions are checked with Rocq 9.1.0. The full build and umbrella
`Require Import OpenSignatures` succeed. Progress, execution preservation, and
type correctness, full normalization, and both coherence claims are proved,
and full preservation has a checked counterexample. The independent
`check-bindings` target imports through `OpenSignaturesExamples`.

| Module | Contents |
| --- | --- |
| [OpenSignaturesSyntax.v](OpenSignaturesSyntax.v) | Stable binder IDs, finite-map contexts, capture-avoiding substitution, and generated helper types and terms. |
| [OpenSignaturesAlpha.v](OpenSignaturesAlpha.v) | Alpha-equivalence setoid, exact comparison, sequential term IDs, and proved table invariants. |
| [OpenSignaturesCore.v](OpenSignaturesCore.v) | Descriptions with bottom, reference `μᴵ`, `close F G`, case analysis, induction, operational and full reduction, conversion, and declarative typing. |
| [OpenSignaturesBinding.v](OpenSignaturesBinding.v) | Substitution support, alpha/free-variable invariance, context scoping, and freshness proofs without metatheory axioms. |
| [OpenSignaturesSubstitution.v](OpenSignaturesSubstitution.v) | Axiom-free alpha compatibility, free-variable support, binder renaming, and substitution composition. |
| [OpenSignaturesProgress.v](OpenSignaturesProgress.v) | Reduction invariants, canonical forms, and progress parameterized only by conversion joinability; no conjectures are imported. |
| [OpenSignaturesElaboration.v](OpenSignaturesElaboration.v) | Open signature assembly, stable constructor identities, local tag translation, empty-payload witnesses, coercion generation, and source elaboration. |
| [OpenSignaturesExamples.v](OpenSignaturesExamples.v) | Lists, nonempty lists, trees, compact/padded rows, source examples, and five checked computations. |
| [OpenSignaturesDerivedTyping.v](OpenSignaturesDerivedTyping.v) | Function/product formation, constant functions, abort, and unroll; weakening is explicit. |
| [OpenSignaturesDataTyping.v](OpenSignaturesDataTyping.v) | Description payload introductions and projections. |
| [OpenSignaturesRowTyping.v](OpenSignaturesRowTyping.v) | Row computation, tuple typing, signatures, and constructors. |
| [OpenSignaturesCaseTyping.v](OpenSignaturesCaseTyping.v) | Handler tuples, row mapping, and case typing. |
| [OpenSignaturesElaborationSoundness.v](OpenSignaturesElaborationSoundness.v) | Simultaneous synthesis/checking/case soundness with explicit premises. |
| [OpenSignaturesCoercionTyping.v](OpenSignaturesCoercionTyping.v) | Row handlers and description coercions with explicit weakening and dead-witness typing. |
| [OpenSignaturesTransport.v](OpenSignaturesTransport.v) | Axiom-free domain formation; derived context exchange and dependent function coercions. |
| [OpenSignaturesSubtypingSoundness.v](OpenSignaturesSubtypingSoundness.v) | Subtyping soundness from weakening, type correctness, operational preservation, and dead-witness typing. |
| [OpenSignaturesExampleTyping.v](OpenSignaturesExampleTyping.v) | Polymorphic list, nonempty-list, and tree definitions and constructors. |
| [OpenSignaturesBindingTests.v](OpenSignaturesBindingTests.v) | Context, substitution, alpha-equivalence, typing, and sequential-ID regressions. |
| [OpenSignaturesConfluence.v](OpenSignaturesConfluence.v) | Closed conversion joinability and confluence via the auxiliary nameless proof and checked encoding/reflection. |
| [OpenSignaturesLabels.v](OpenSignaturesLabels.v) | Closed uniqueness of row label resolution. |
| [OpenSignaturesTypingEncoding.v](OpenSignaturesTypingEncoding.v) | Typed encoding/reflection gives axiom-free weakening, substitution, and type correctness. |
| [OpenSignaturesBeta.v](OpenSignaturesBeta.v) | Beta preservation for the named calculus, independent of full preservation. |
| [OpenSignaturesPreservation.v](OpenSignaturesPreservation.v) | Axiom-free operational preservation, using all root computation rules and evaluation contexts. |
| [OpenSignaturesInductionBeta.v](OpenSignaturesInductionBeta.v) | Axiom-free root preservation for close induction and close cases. |
| [nameless/DBEtaPostponement.v](nameless/DBEtaPostponement.v) | Axiom-free strong eta postponement and factorization of typed full reductions. |
| [nameless/DBDescriptionViews.v](nameless/DBDescriptionViews.v) | Typed constructor views; closes dead-witness and elaboration soundness without full preservation. |
| [nameless/DBActiveParallel.v](nameless/DBActiveParallel.v), [DBActivePostponement.v](nameless/DBActivePostponement.v) | Parallel steps record actual computation, and eta postponement preserves that activity. |
| [nameless/DBNormalization.v](nameless/DBNormalization.v), [OpenSignaturesNormalization.v](OpenSignaturesNormalization.v) | Computation-to-full termination transfer and the completed semantic normalization bridge to named terms. |
| [nameless/DBComputationSubstitution.v](nameless/DBComputationSubstitution.v) | Substitution preserves individual computation steps and reflects normalization. |
| [nameless/DBReducibility.v](nameless/DBReducibility.v) | Reducibility candidates and introduction lemmas for dependent functions and pairs. The full semantic fundamental theorem is proved in `DBSemanticFundamental.v`. |
| [nameless/DBFullReductionStructure.v](nameless/DBFullReductionStructure.v), [DBFullNormalForms.v](nameless/DBFullNormalForms.v) | Full beta/eta binding lemmas and a checked normalizer given accessibility. |
| [nameless/DBFullReducibility.v](nameless/DBFullReducibility.v) | Function and pair candidates for full reduction, including eta contraction. |
| [nameless/DBSemanticTypes.v](nameless/DBSemanticTypes.v), [DBUniverseModel.v](nameless/DBUniverseModel.v) | Conversion-coherent type interpretation and cumulative universes over a level-indexed atomic model. |
| [nameless/DBPositiveCandidates.v](nameless/DBPositiveCandidates.v) | Positive candidate fixed points with fold, unfold, and induction laws. |
| [nameless/DBIndexedCandidates.v](nameless/DBIndexedCandidates.v) | Fixed points restricted to computable indices, refinement, and semantic coherence. |
| [nameless/DBDescriptionCandidates.v](nameless/DBDescriptionCandidates.v), [DBEnumCandidates.v](nameless/DBEnumCandidates.v) | Computable description values and enumeration positions, including the empty enumeration. |
| [nameless/DBDescriptionModel.v](nameless/DBDescriptionModel.v) | Every computable description has a unique positive semantic functor preserving candidates. |
| [nameless/DBSmallTypeModel.v](nameless/DBSmallTypeModel.v), [DBCalculusModel.v](nameless/DBCalculusModel.v) | Concrete small atomic types and cumulative universes, with semantic formation of descriptions, reference fixed points, and closure. |
| [nameless/DBSemanticGeneration.v](nameless/DBSemanticGeneration.v) | Semantic inversion for universes, functions, and pairs, guarding substituted codomains by normalization. |
| [nameless/DBSemanticBinders.v](nameless/DBSemanticBinders.v), [DBSemanticJudgments.v](nameless/DBSemanticJudgments.v) | Stable codomain candidates and semantic rules for functions, pairs, universes, variables, and conversion. |
| [nameless/DBSemanticVariance.v](nameless/DBSemanticVariance.v) | Semantic validity of function cumulativity, using comparison depth preserved by substitution and reduction. |
| [nameless/DBSemanticSubstitution.v](nameless/DBSemanticSubstitution.v) | Simultaneous substitution, semantic environments, full-step preservation, and normalization reflection. |
| [nameless/DBHeadExpansion.v](nameless/DBHeadExpansion.v), [DBBetaExpansion.v](nameless/DBBetaExpansion.v) | Shared head and beta expansion for full-reduction candidates. |
| [nameless/DBInterpretationComputability.v](nameless/DBInterpretationComputability.v), [DBAllComputability.v](nameless/DBAllComputability.v), [DBHypsComputability.v](nameless/DBHypsComputability.v) | Semantic computation of description interpretation and recursive hypotheses. |
| [nameless/DBEnumComputability.v](nameless/DBEnumComputability.v), [DBSwitchComputability.v](nameless/DBSwitchComputability.v) | Enumeration products and switching at every universe level. |
| [nameless/DBSaturatedElimination.v](nameless/DBSaturatedElimination.v), [DBCloseCaseComputability.v](nameless/DBCloseCaseComputability.v) | Dependent elimination from saturated constructors and semantic close-case computation. |
| [nameless/DBEliminatorCandidates.v](nameless/DBEliminatorCandidates.v), [DBIndComputability.v](nameless/DBIndComputability.v) | Candidate refinements and semantic induction on reference fixed points. |
| [nameless/DBDataComputability.v](nameless/DBDataComputability.v), [DBCloseIndComputability.v](nameless/DBCloseIndComputability.v) | Computable definitions, semantic fold/unfold, and close induction for arbitrary outer signatures. |
| [nameless/DBSemanticFamilies.v](nameless/DBSemanticFamilies.v), [DBSemanticData.v](nameless/DBSemanticData.v), [DBSemanticCloseMethods.v](nameless/DBSemanticCloseMethods.v) | Semantic interpretation of families, definitions, motives, and induction methods. |
| [nameless/DBSemanticOperators.v](nameless/DBSemanticOperators.v), [DBSemanticPrimitiveRules.v](nameless/DBSemanticPrimitiveRules.v), [DBSemanticCloseCase.v](nameless/DBSemanticCloseCase.v) | Semantic validation of every remaining typing rule. |
| [nameless/DBSemanticFundamental.v](nameless/DBSemanticFundamental.v) | Full fundamental typing theorem, inhabited semantic environments, and strong normalization without assumptions. |
| [nameless/DBCumulativeTyping.v](nameless/DBCumulativeTyping.v), [DBTypeComparison.v](nameless/DBTypeComparison.v), [DBTypedPiViews.v](nameless/DBTypedPiViews.v) | Checked type changes, structural comparison modulo conversion, comparison strengthening, and typed Pi views. |
| [nameless/DBEtaPrincipal.v](nameless/DBEtaPrincipal.v) | Eta preservation for arbitrary variable typings and functions with a stable principal type; general eta preservation remains open. |
| [nameless/DBFullPreservation.v](nameless/DBFullPreservation.v) | Full preservation reduced to an explicit general eta-preservation premise; the premise is refuted by `DBEtaPolymorphism.v`. |
| [OpenSignaturesPayloadInversion.v](OpenSignaturesPayloadInversion.v) | Axiom-free inversion of close constructors. |
| [OpenSignaturesEtaRegression.v](OpenSignaturesEtaRegression.v) | Axiom-free checks for function codomain and domain cumulativity, eta reduct typing, and distinct universes. |
| [OpenSignaturesObservations.v](OpenSignaturesObservations.v), [OpenSignaturesObservationalLaws.v](OpenSignaturesObservationalLaws.v), [OpenSignaturesObservationalTypes.v](OpenSignaturesObservationalTypes.v) | Closing substitutions, Boolean observations, conversion adequacy, equivalence laws, and typed contextual congruence. |
| [OpenSignaturesEtaPolymorphism.v](OpenSignaturesEtaPolymorphism.v), [nameless/DBEtaPolymorphism.v](nameless/DBEtaPolymorphism.v) | Axiom-free refutation of unrestricted eta/full preservation by a polymorphic application. |
| [OpenSignaturesComputationPreservation.v](OpenSignaturesComputationPreservation.v) | Preservation for compatible computation, including binders and annotations; a separate checked repair option. |
| [OpenSignaturesRowCoherence.v](OpenSignaturesRowCoherence.v) | Live handler uniqueness and pointwise conversion of row maps on every closed input for fixed row views. |
| [OpenSignaturesRelBase.v](OpenSignaturesRelBase.v) … [OpenSignaturesRelFundamental.v](OpenSignaturesRelFundamental.v) | Binary relational model on closed terms: conversion-closed PERs at structurally related types, cumulative universes, description functors with least fixed points, close types, and the fundamental lemma for every typing rule. |
| [OpenSignaturesRelAdequacy.v](OpenSignaturesRelAdequacy.v) | Related terms give the same observations, hence `observational_eq`. |
| [OpenSignaturesRelViews.v](OpenSignaturesRelViews.v), [OpenSignaturesRelGraph.v](OpenSignaturesRelGraph.v), [OpenSignaturesRelGraphFunc.v](OpenSignaturesRelGraphFunc.v), [OpenSignaturesRelGraphComp.v](OpenSignaturesRelGraphComp.v) | Semantic coercion graphs with name-based row retagging: closure, transport, functionality, totality, and composition. |
| [OpenSignaturesRelCoercion.v](OpenSignaturesRelCoercion.v), [OpenSignaturesRelElab.v](OpenSignaturesRelElab.v) | Realizability of every coercion derivation, and elaboration coherence over contexts linked by related types. See [RELATIONAL_PLAN.md](RELATIONAL_PLAN.md). |
| [OpenSignaturesTheorems.v](OpenSignaturesTheorems.v) | Forty-six closed claims, including both coherence theorems, and the exact refuted full-preservation proposition. |
| [OpenSignaturesAudit.v](OpenSignaturesAudit.v) | Rule signatures and assumption checks, beginning with `context_validity`. |
| [PROOF_START.md](PROOF_START.md) | First theorem, proof approach, and acceptance criteria. |

Prior proofs, the unfinished progress development, and generated artifacts
are saved in [proof-archive/2026-09-24](../proof-archive/2026-09-24/README.md).
The active build includes no archive modules or previous proof implementations.

The main closure rule is implemented directly:

```text
xs : ⟦F i⟧ (close G G)
──────────────────────
in xs : close F G i
```

The raw syntax retains the implicit index type as an explicit argument to
generic operators. `close` types never unfold by conversion. Recursive
induction uses the diagonal motive `P G j y` for children, and its recursive
call uses outer definition `G`. One-layer `closeCase` supports motives at
every universe level; recursive induction is small, as in the sketch.

The core has no constructor-subtyping relation. `sub` in the elaboration
module generates a core function. Live row branches keep their payload and
translate their tag by constructor identity. Impossible source branches
generate empty elimination, including when no target position exists.
Dependent function coercions substitute the converted argument into the
source codomain and choose fresh numeric binders to avoid capture.

The modeled source syntax accepts description-valued constructor schemes:
the positive recursive binder has already been represented by `TIVar`.
It specifies the theory boundary rather than a parser for the proposed
surface notation. Raw `ECore` terms are checked-only; an annotation is
required to synthesize their type. Guessing a declarative type for an
unannotated core `in` could assign it different constructor identities.

The elaboration relations permit explicit derivations and checked
emptiness witnesses. They are not a deterministic implementation of
inference or a decision procedure for semantic inhabitation. Source case
results are nondependent; the core case eliminator itself is dependent.

The theorem statements cover context validity, substitution, preservation,
progress, full beta/eta normalization and confluence modulo alpha, consistency,
canonical forms, closure elimination, name resolution, coverage, emptiness,
coercion typing, elaboration soundness, coherence, and concrete example
typing. Coherence is observational and quantified over typed closing
substitutions; it does not assert that alternative coercions are
definitionally equal. Both coherence theorems are proved through the
binary relational model. A deterministic policy for dependent inference and
a semantic construction relating the diagonal to reference `μᴵ` remain
design obligations.

Five current example proofs check singleton head, tail, widening, a
compact/padded round trip, and preservation of a free payload ID. The
binding regressions also exercise shadowing, capture avoidance, alpha
comparison, stable lookup, and ID reuse. The active development declares
no metatheory conjectures. The ten older computation proofs remain in the
archive.

Function cumulativity repairs the known eta counterexamples. See the axiom-free [regressions](OpenSignaturesEtaRegression.v), the [updated rules](type-rules.md), and [remaining proof obligations](PROOF_STATUS.md).
