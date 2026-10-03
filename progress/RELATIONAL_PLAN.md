# Relational model for the coherence conjectures

Goal: prove `coercion_coherence` and `checking_coherence` in
`OpenSignaturesTheorems.v` with their original statements, no axioms.

**Status: done.** Both are proved and the audit prints `Closed under the
global context`.

## Why a model is needed

`observational_eq` quantifies over arbitrary typed Boolean contexts. Pointwise
conversion of coercions on closed inputs (already proved) does not give
contextual equivalence. Dependent function coercions make the two codomain
coercions have *different* source types `B[c1 y]` and `B[c2 y]`; transitivity
introduces unrelated middle types. A syntactic simulation cannot track the
row names needed for retagging across such heterogeneous types. A binary
logical relation on closed terms handles both: type relatedness is structural
(so enum codes, hence row names, agree) and heterogeneous types are native.

## Design (all on closed named terms, conversion-closed, no SN needed)

- `rel := term -> term -> Prop`. Relations are PERs closed under `conv`.
- Canonical relations: `unit_rel`, `tag_rel`, `code_rel` (literal enum codes),
  `enum_rel n` (positions `< n`), `pi_rel RA RB` (closed related arguments),
  `sigma_rel RA RB` (conv to `TPair` with closed components), `roll R`
  (conv to `TIn` with closed payload), `empty_rel`.
- `TI2 atom A B R`: structural binary type interpretation, generic over an
  atom interpretation for non-Pi/Sigma canonical heads. Clauses: atom, pi,
  sigma, equiv. Lemmas: conv-invariance, uniqueness in either component,
  PER, symmetry, transitivity.
- `desc2 atom RI D D' F`: description codes interpreted as monotone
  functors on index families (single-index families respecting `RI`).
  Choice codes require literal enum codes, so names agree.
- `mu_rel RI F i`: impredicative least fixed point over respectful families.
- `small_atom2`: nested inductive (unit, uid, enum codes, enums, MuAt,
  CloseAt) like `nameless/DBSmallTypeModel.v`.
- Universe tower: list of level relations like `nameless/DBUniverseModel.v`;
  `TIDesc` from level 1.
- Fundamental lemma over named typing with `closing2 Gamma g1 g2`
  (related closed environments). Structured as one semantic lemma per typing
  rule so elaboration coherence can reuse them.
- Adequacy: related terms of `observation_type` convert to the same position,
  hence evaluate to the same observation. Gives `observational_eq`.
- Coercions: semantic coercion graphs `SubG A B Co` (functional, total via
  realizers), clauses eq / empty / pi / close. Composition lemma (semantic cut
  elimination) handles `su_trans`. Graph uniqueness for structurally related
  types gives coherence.
- Elaboration: each check result is a graph realizer applied to a synthesized
  result; structural rules are syntax directed. Pairwise induction.

## Files (planned order)

1. `OpenSignaturesRelBase.v`: relations, codes, conv inversion lemmas.
2. `OpenSignaturesRelTypes.v`: generic `TI2` and its lemmas.
3. `OpenSignaturesRelDesc.v`: `desc2`, functors, `mu_rel`.
4. `OpenSignaturesRelModel.v`: small atoms, universe tower.
5. `OpenSignaturesRelFundamental*.v`: semantic rules and fundamental lemma.
6. `OpenSignaturesRelAdequacy.v`: observational consequences.
7. `OpenSignaturesRelCoercion.v`: graphs, coercion coherence.
8. `OpenSignaturesRelElaboration.v`: checking coherence.

## Status

- [x] `OpenSignaturesRelBase.v`: relations, conversion inversion lemmas.
- [x] `OpenSignaturesRelFix.v`: families, functors, least fixed points
  (closed indices only; respect includes index conversion).
- [x] `OpenSignaturesRelSmall.v`: mutual `S2`/`D2`, inductive shape views.
- [x] `OpenSignaturesRelSmallClaims.v`: PER, conversion closure, symmetry,
  uniqueness in either component, transitivity, for `S2` and `D2`.
- [x] `OpenSignaturesRelLevels.v`: generic structural closure `TI2` with all
  laws under atom hypotheses; level atoms; tower `levels`/`interp`/`univ_rel`;
  cumulativity; cross-level uniqueness; `S2_interp`, `interp0_S2`.
- [ ] `OpenSignaturesRelSem.v`: `rel_at`, `ty_rel`, canonical relations
  (left-canonical `canonT`, `canonL` for functors, avoids choice), semantic
  rule per typing rule on closed terms.
- [x] Semantic rules: `RelSem` (core, enums, switch, description formers),
  `RelData` (TInterp via functors, MuAt/CloseAt types and constructors,
  close case), `RelElim` (TIAll, THyps, TInd, TCloseInd induction),
  `RelRules` (rule-level forms, function cumulativity via depth-indexed ule).
- [x] `RelInst`/`RelEnv`/`RelDerived`/`RelSubst`: closed environments,
  `closing2`, derived forms up to alpha via encoding, substitution commutation.
- [x] `OpenSignaturesRelFundamental.v`: `rel_fundamental` over all 43 typing
  rules, closed under the global context.
- [x] `OpenSignaturesRelAdequacy.v`: related terms at the observation type
  evaluate to the same observation; `rel_observational` gives `observational_eq`.
- [x] `OpenSignaturesRelViews.v`: inversion views at enum types, enum-tagged
  sums and close types; related types `rty` and retyping.
- [x] `OpenSignaturesRelGraph*.v`: coercion graphs `Gr` (eq, empty, pi with
  closed realizers, sum retagging by row name, roll), closure, transport along
  related types, absorption, functionality, totality, canonical graph, and
  composition (semantic transitivity elimination).
- [x] `OpenSignaturesRelCoercion.v`: every `sub` derivation realizes a graph
  (`sub_real`, `desc_real`); `coercion_coherence_rel`, closed under the global
  context.
- [x] `OpenSignaturesRelElab.v`: elaboration coherence over linked contexts
  (`link`, type agreement on the pair and both diagonals, peeled target
  conversions); `checking_coherence_rel`, closed under the global context.
- [x] `OpenSignaturesTheorems.v`: both conjectures replaced by theorems.

Notes: Ltac cannot match hypotheses under binders; use named destruct
patterns on the inductive views. `repeat split` descends into
`rel_equiv`/`per`; use `repeat apply conj` or exact `refine` splits.
`length` is shadowed by `String.length`; write `List.length`.
