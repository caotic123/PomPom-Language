# Full preservation: annotated repair in progress

**September 30 decision:** the user selected explicit core annotations while
retaining general eta contraction. The repair is being implemented in
[annotated/](annotated/README.md). Its complete annotated syntax and typing
rules, binding algebra, erasure, weakening, substitution, type-comparison
transport, and beta preservation are checked without axioms. A typed regression
shows that annotations expose the counterexample's hidden binder dependency
and reject its bad eta contraction. General eta preservation and migration of
the public calculus are still unfinished; the original claim is not counted
as proved by these supporting results.

The original `full_preservation` proposition is **false under the current
rules**, including the function-cumulativity repair. It is retained as
`full_preservation_statement`, not asserted as an axiom. The independent
[refutation](OpenSignaturesEtaPolymorphism.v) is kernel checked and imports
no public conjectures. The original-claim status is 44 proved, two open
coherence claims, and one refuted claim.

## Counterexample

Let

```text
f = (lambda z. lambda B. z) (lambda x. x)
T = Pi A : Sort 0. A -> A
```

Then `lambda A. f A : T`, and unrestricted eta reduction contracts it to
`f`. But `f : T` has no typing derivation.

Inside the eta-expanded binder, the identity argument can receive the type
`A -> A`. The local binding `z` therefore has that type, and the application
returns it. In `f` itself, `z` must receive its type before the binder `B`
is introduced. It cannot receive the type `B -> B` needed for every `B`.

The Rocq proof in [nameless/DBEtaPolymorphism.v](nameless/DBEtaPolymorphism.v)
inverts application, lambda, and variable typing, including every conversion
and cumulativity chain. A hypothetical typing yields a raw type comparison
from `lift 1 0 C` to `Pi (Var 0) (Var 1)`. Substituting `UnitT` and `Sort 0`
for that variable forces the same function domain to be above both types.
Pi variance and rigid-head separation rule this out. No normalization or
unproved strengthening principle is used.

The named module transfers the positive derivation through typing reflection
and the negative result through typing encoding. Its
`full_preservation_refuted` theorem negates the exact original proposition.

```sh
make -C progress check-eta-polymorphism
rocq check -silent -Q progress '' OpenSignaturesEtaPolymorphism
```

## Previously considered repairs

Keeping current typing permits the already-proved preservation theorem for
computation, with beta/eta conversion and normalization retained separately.
The concrete alternative is proved as
`named_computation_preservation` in
[OpenSignaturesComputationPreservation.v](OpenSignaturesComputationPreservation.v).
Its `computation` relation contains all root computations and every compatible
context, including binders and type annotations. It includes operational
`step` and is contained in the original beta/eta `reduction`. The proof
encodes the step, applies the checked nameless computation theorem, and
reflects typing back. This module does not alter the original relations or
rename the false claim. Adopting it as the replacement requirement would
explicitly revise that requirement; it does not prove the original claim.

The selected repair retains unrestricted eta on explicitly annotated core
terms. Annotations retain the hidden dependency and prevent this particular
contraction. See the [implementation and remaining work](annotated/README.md).

Merely requiring the eta reduct to be a value is not a drop-in repair:
that side condition is not stable under arbitrary substitution, so the
confluence proof would also need reconsideration. Adding a typing rule that
assumes eta preservation would likewise not prove it from the current rules.

The following checked supporting results remain valid, but cannot discharge
the false general premise.

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

## Limit of the principal-type argument

An eta-expanded typing gives typings of `f` in the extended context. In the
counterexample, the hidden type of the identity argument depends on that
binder. Stable principality is unavailable, and the target polymorphic type
cannot be reconstructed. The proved variable/lambda cases and comparison
library therefore remain useful restricted results, not a route to the
original universal claim without a rule change.
