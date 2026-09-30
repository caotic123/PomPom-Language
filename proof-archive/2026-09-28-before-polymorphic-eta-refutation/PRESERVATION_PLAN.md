# Remaining full-preservation proof

The original `full_preservation` statement is unchanged and remains a
conjecture. Operational preservation and full beta/eta normalization are
proved without assumptions. The original audit count is 44/47; the other
two open claims are coercion coherence and checking coherence.

## Checked reduction of the problem

`DBFullPreservation.full_preservation_from_eta` proves all computation and
congruence cases with one explicit premise:

```coq
forall Gamma f T,
  typing Gamma (TLam (TApp (lift 1 0 f) (TVar 0))) T ->
  typing Gamma f T.
```

`DBRootPreservation.eta_lambda_preservation` proves this when `f` is a
lambda, by beta reduction under the outer binder.
`DBEtaPrincipal.eta_variable_preservation` proves it when `f` is any
variable, at arbitrary dependent function types and through arbitrary
chains of conversion and universe comparison.

## Comparison library

- `DBCumulativeTyping.v`: `type_change Gamma A B` records checked conversion
  and universe-comparison chains, with formation of intermediate types.
  The library proves typing transport, context narrowing, and dependent Pi
  variance for these chains.
- `DBTypedPiViews.v`: `typed_pi_view` recovers a well-typed Pi representative
  from a type convertible to a Pi. Computation/eta factorization avoids any
  use of general eta preservation.
- `DBTypeComparison.v`: `type_comparison A B` is raw structural comparison
  modulo conversion. Its constructors compare convertible endpoints,
  universes, or dependent Pi components. It is transitive and preserved by
  substitution. `comparison_realization` turns a raw comparison into a
  checked `type_change` using only formation of its endpoints. The proof
  uses typed Pi views and recursively lifts comparisons through Pi.
  `type_change_strengthening` removes a variable from comparison endpoints;
  it does not assert strengthening of arbitrary typing derivations.

## Principal-type eta argument

`DBEtaPrincipal.stable_principal Gamma f S` states that every typing of
`lift 1 0 f` in an extended context is above `lift 1 0 S` in the raw
comparison relation. `eta_principal_preservation` proves general eta
contraction from this property and `typing Gamma f S`.

The proof inverts the function application and its conversion/cumulativity
chain, compares the argument variable to the principal domain, and removes
the extra binder from that comparison by substitution. Pi variance then
reconstructs the requested type of `f`. No strengthening of arbitrary
term typing is assumed.

The property is proved for variables, preserved by application and
conversion of the principal type, and supplied by `explicit_principal`
for `MuI`, `Close`, `Switch`, `Ind`, `Hyps`, `CloseCase`, and `CloseInd`.
For explicit primitives, `explicit_principal_generation` also recovers
the principal typing in any context where the term is already typed.

## Work still required

An eta-expanded typing gives typings of `f` in the extended context. It
does not immediately give a typing of `f` in the original context.
Unannotated lambdas, pairs, and applications can use intermediate types
that depend on the removed variable. Proving arbitrary term strengthening
requires an argument beyond the comparison-strengthening theorem above.
Stable principality must also be established or replaced for arbitrary
function expressions, especially applications with lambda heads and
projections from implicit pairs.

Do not replace these obligations with a circular eta-typing rule, assume
that semantic computability implies syntactic typing, or claim that
normalization supplies subject expansion. None of those steps is proved.

After general eta preservation is proved, instantiate
`full_preservation_from_eta`, transport the result through named/nameless
encoding and reflection, replace the original conjecture with its proof,
and rerun the complete assumption audit and kernel check.
