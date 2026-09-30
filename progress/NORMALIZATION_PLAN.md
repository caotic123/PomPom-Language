# Completed normalization proof

The original unrestricted `normalization` statement in
`OpenSignaturesTheorems.v` is proved for every typing derivation and full
beta/eta reduction. The audit reports 44 closed claims without assumptions
and two coherence conjectures; full preservation is separately refuted. No original statement or calculus rule was changed by
the semantic-model work below.

## Checked components

The basic libraries are `DBFullReductionStructure.v`, `DBFullNormalForms.v`,
`DBFullReducibility.v`, `DBSemanticTypes.v`, and `DBUniverseModel.v`. They give
full-reduction candidates, conversion-coherent dependent type meanings, a
normalizer requiring accessibility, and the numeric universe construction.

The concrete model is now defined and its supporting theorems compile:

- `DBIndexedCandidates.v`: positive fixed points restricted to a validity
  predicate on indices. Candidate, fold, unfold, refinement, index coherence,
  and model-equivalence theorems are proved. `totalize` extends a partial family
  constructively, without deciding validity or identifying its proofs.
- `DBDescriptionCandidates.v`: `description_computable atom RI D` has raw
  introduction cases, reduction closure, and neutral closure. Pi/Sigma/choice
  constructors control the original function applied to every computable
  argument. Its candidate theorem needs no assumptions about `atom`.
- `DBEnumCandidates.v`: canonical position predicates from enumeration normal
  forms. The empty enumeration uses the least candidate. `enum_elements` is a
  candidate for every raw enumeration, and conversion preserves its meaning.
- `DBDescriptionModel.v`: `description_interp atom RI D F` associates a positive
  semantic functor with a normalizing description and its normal form. Its
  meaning is unique, even across different index predicates. It preserves
  candidates and inclusions. Every computable description has a meaning when
  the index predicate is a candidate and the atom model is coherent.
  Canonical `description_elements` avoids choosing a functor separately for
  each argument.
- `DBSmallTypeModel.v`: nested positive `small_atom` covers unit, identifiers,
  enumeration universes/positions, reference fixed points, and closure.
  The fixed-point constructors carry candidate certificates; the introduction
  theorems discharge them using the description model. `small_atom_unique`
  uses guarded recursion through the nested interpretations and is axiom-free.
- `DBCalculusModel.v`: `primitive_at` embeds small atoms at every level and
  admits description types only from level 1. `calculus_interp`,
  `calculus_type`, and `calculus_elements` instantiate the coherent cumulative
  universe hierarchy. Level zero interpretations correspond to `small_atom`.
  Concrete formation lemmas cover unit, identifiers, enums, descriptions,
  reference fixed points, and closure. Pi/Sigma formation comes from the
  universe hierarchy.
- `DBSemanticGeneration.v`: inversion for universe, function, and pair
  interpretations. Pi/Sigma inversion currently returns a codomain
  interpretation guarded by normalization of the original substituted
  codomain; it does not assert that substitution preserves raw normalization.

The primitive semantic operators now also compile without axioms:

- `DBHeadExpansion.v` shares the accessibility proof for independent argument
  reductions; `DBBetaExpansion.v` proves candidate beta expansion and the
  computability of two nested lambdas.
- `DBInterpretationComputability.v`, `DBAllComputability.v`, and
  `DBHypsComputability.v` prove `Interp`, `IAll`, and `Hyps` computable.
  The latter two take a stable indexed candidate family, allowing a refinement
  of recursive children rather than requiring the whole family to be the
  interpretation of the syntactic carrier annotation.
- `DBEnumCandidates.v` now also interprets enumeration codes by
  `enumeration_computable`, whose constructors retain computable tails.
  `DBEnumComputability.v` and `DBSwitchComputability.v` prove `EPi` and `Switch`
  computable at every universe level.
- `DBSaturatedElimination.v` gives dependent elimination from a saturated set
  of constructors; `DBCloseCaseComputability.v` instantiates it for `CloseCase`
  with arbitrary candidate motives, including motives above universe zero.
- `DBEliminatorCandidates.v` proves the candidate law for refinements storing
  computability of an eliminator with independently reducing parameters.
  `DBIndComputability.v` uses it to prove `Ind` computable by fixed-point
  induction. Recursive `Hyps` calls are justified on refined children.
- `DBDataComputability.v` supplies computable definitions and semantic
  fold/unfold. `DBCloseIndComputability.v` proves `CloseInd` computable: it
  first proves the recursive diagonal by candidate refinement, then eliminates
  an arbitrary outer signature by saturation. Its two reference-definition
  occurrences may reduce independently.

## Implementation details to preserve

1. `type_interp_unique` and `description_interp_unique` are deliberately
   transparent (`Defined`). Normal-form equalities preserve the left
   interpretation derivation: replace right variables with left variables,
   using `subst m` or `injection HE as <- <-`. Rewriting the left proof loses
   structural descent and makes the nested `small_atom_unique` recursion fail
   Rocq's guard checker. `description_domain_unique` must also stay transparent.
2. Description meanings normalize recursive index expressions before selecting
   a family component. `small_fixed_point_index_equiv` proves that convertible
   computable indices have equivalent fixed-point predicates.
3. The interpretation of `close F G` is one rolled layer of F over the positive
   fixed point for G. Its diagonal is semantically equivalent to that fixed
   point by fold/unfold; this does not add a judgmental equation to the syntax.
4. `full_SN` alone does not make a function computable. For example, a raw
   normalizing function can reduce to a constant while an earlier application
   duplicates an argument into a divergent subterm. Keep the original
   pointwise computability premises in `description_computable`.
5. Atomic/model premises are ordinary theorem arguments. No new axiom,
   admitted obligation, choice, or proof-irrelevance principle was introduced.

## Judgment bridge now checked

`DBSemanticBinders.v` exposes the normalized codomain behind Pi/Sigma
interpretations, with unconditional candidate and stability laws. Interpretation
of the *original* substituted codomain still requires its normalization.
`DBSemanticJudgments.v` defines `semantic_value t A` as membership in an
interpreted type at some universe level. Its checked rules cover universes,
Pi/Sigma formation, lambda/application, pairs/projections, conversion, variables,
and sort cumulativity. `DBSemanticVariance.v` validates function cumulativity:
a height-bounded universe comparison is preserved by substitution and
synchronized reduction, and its height supports semantic variance induction
after normalization. Lambda and pair introduction use the strengthened
binder views; no substitution-normalization assumption was added.

## Fundamental theorem and named result

`DBSemanticSubstitution.v` supplies simultaneous substitution, semantic
environments, environment extension, full-step preservation, and normalization
reflection. `DBSemanticFamilies.v`, `DBSemanticData.v`, and
`DBSemanticCloseMethods.v` interpret families, definitions, motives, and
methods. `DBSemanticOperators.v`, `DBSemanticPrimitiveRules.v`, and
`DBSemanticCloseCase.v` bridge every primitive typing constructor.

`DBSemanticFundamental.v` proves `semantic_fundamental` by induction on all
typing rules. Its explicit result-formation premises supply computability of
original substituted result types. Binder cases extend the semantic
environment; the remaining cases use bounded proof search over the checked
semantic rules. `semantic_environment_inhabited` extends well-formed contexts
with computable variables. `typing_full_normalization` then reflects
accessibility from an instantiated term back to the original term.

`OpenSignaturesNormalization.named_full_normalization` uses typed encoding
and accessibility reflection to prove the original named statement. The public
`normalization` theorem applies this bridge. The proof covers reduction under
binders and annotations as well as beta, eta, and all primitive computations.
Its dependencies pass an independent kernel check without axioms.

Normalization also closes `consistency`, `canonical_forms_named`,
`dead_close_uninhabited`, `close_roll_unroll`, `no_uniform_list_downcast`, and
`self_restricted_list_empty`.

## Other original obligations

General syntactic eta preservation, required by the original full-preservation
claim, is refuted by `OpenSignaturesEtaPolymorphism.v`.
Semantic eta equivalence of candidates does not imply typing preservation.
Coercion coherence and checking coherence remain separate obligations;
normalization alone does not prove either.
