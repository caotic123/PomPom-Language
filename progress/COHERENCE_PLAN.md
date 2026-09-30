# Remaining coherence proofs

`coercion_coherence` and `checking_coherence` retain their original
statements and remain conjectures. The separate full-preservation claim is now refuted;
its false axiom was removed. Strong normalization, consistency,
subtyping soundness, and checking/synthesis soundness are all proved
without assumptions. The original-claim count remains 44/47.

## Independent observation library

`OpenSignaturesObservations.v` contains the original definitions of
`instantiate`, `closing`, `observation_type`, `observation`,
`closed_observational_eq`, and `observational_eq`. Their meanings are
unchanged. The original public `closing_substitution` theorem is a wrapper
around `named_closing_substitution` in this module.

The module also contains the existing closed observation normalization and
conversion-adequacy proofs. Its internal termination lemma uses proved
named full normalization and operational preservation. It does not import
`OpenSignaturesTheorems.v` or any conjecture.

`OpenSignaturesObservationalLaws.v` proves:

- Reflexivity, symmetry, and transitivity for closed and open equivalence.
- `closed_observational_function_tests`: the contextual definition is
  equivalent to testing with all closed functions into the Boolean
  observation type. This is a reformulation of observations, not a theorem
  that pointwise equal functions are contextually equal.
- `compose_coercion_beta`: the generated composition computes to successive
  applications, using freshness of its generated binder.
- `closed_observational_congruence`: applying one typed closed function to
  equivalent closed arguments preserves equivalence.
- `closed_observational_context`: substitution into one typed context with
  a fixed closed result type preserves equivalence.

`OpenSignaturesObservationalTypes.v` proves invariance under conversion of
the observed type, for both closed and open contextual equivalence. It also
proves application congruence when both functions and arguments are
contextually equivalent at fixed nondependent function and argument types.

## Checked row behavior

`OpenSignaturesRowCoherence.v` proves that any inhabited closed source payload
selects a live handler. A dead handler would produce a closed bottom inhabitant,
contradicting normalization and canonical forms. Target-label uniqueness makes
the selected position independent of the handler derivation.

`row_payload_canonical` normalizes any closed inhabitant of a row interpretation
to a pair of a known enum position and a well-typed branch payload.
`row_maps_closed_pointwise_coherence` then proves raw conversion of the outputs
of two row-handler derivations on every closed input, for the same source and
target row views. These proofs import no public conjectures.

`OpenSignaturesRowViews.v` proves that convertible row views preserve every
label position and give convertible branch descriptions.
`OpenSignaturesDescriptionCoherence.v` uses this to prove
`description_coercions_closed_pointwise_coherence`: any two description
coercions agree by raw conversion on every closed typed input. The proof covers
all three constructors (`ds_conv`, `ds_dead`, `ds_rows`), arbitrary convertible
source and target row views, and alternative dead/live handler derivations.
It also proves that a description coercion between convertible descriptions
acts as identity on closed inputs.

These checked pointwise theorems do not supply contextual function
extensionality or transport arbitrary open derivations through closing
environments. Those remain necessary for the original coherence statements.

## Required arguments

Function extensionality for contextual equivalence is still needed, or an
alternative logical relation that proves the necessary function cases and
is adequate for Boolean observations. Congruence alone does not establish
extensionality. The dependent function cases must account for related
arguments appearing in codomains.

For description coercions, prove that live row handlers preserve payloads
and constructor identity, including composition through intermediate rows.
The checked `label_resolution_unique` result controls positions across
convertible row views. Dead handlers are irrelevant on closed inhabitants
by the proved consistency and dead-soundness results.

Coercion coherence must cover conversion, transitivity, bottom elimination,
dependent function coercions, and close coercions. Checking coherence then
requires a simultaneous argument for synthesis, checking, and case handlers;
dependent application result types vary with elaborated arguments. The
checked-only `ECore` rule is part of the existing repaired specification.

Do not assume all coercions are definitionally equal. Row maps and identity
coercions can require data extensionality on closed arguments. Preserve the
quantification over typed closing substitutions and typed Boolean contexts.
