# Proof status

All 47 original statements and the calculus rules are unchanged. Twenty-seven
claims have proofs without axiom dependencies, 16 have checked proofs
using existing conjectures, and 4 remain conjectures. The metatheory is
**not complete**. Moreover, `full_preservation` is false for the current rules: an axiom-free counterexample is checked in [OpenSignaturesEtaCounterexample.v](OpenSignaturesEtaCounterexample.v).

## Progress, preservation, and normalization

| Claim | Checked result | Remaining assumptions |
| --- | --- | --- |
| `progress` | Induction over every typing rule, with canonical forms and proved conversion joinability. | None |
| `preservation` | Operational steps are full reductions; its existing proof is conditional. | Refuted `full_preservation` assumption |
| `preservation_eval` | Induction over evaluation. | `full_preservation` |
| `normalization` | Still a conjecture about accessibility of full reduction. | Unproved |
| `normalization_eval` (supporting theorem) | Strong normalization supplies enough evaluator fuel; progress identifies the terminal result as a value. | `normalization`, `full_preservation` |
| `confluence` | Parallel beta/computation and eta diamonds, commutation, and an encoding/reflection proof for named terms. | None |
| `consistency` | Normalize a hypothetical bottom inhabitant and exclude bottom values. | `normalization`, `full_preservation` |

Progress, confluence, and conversion joinability have no axiom dependencies. The progress argument
constructs type-formation evidence directly from the typing rules. An
invariant for enum-product and description computations avoids using
preservation to classify their results.

The other results remain conditional until their listed assumptions are discharged.
In particular, deriving weak preservation from full preservation does not
solve the subject-reduction obligation.

## Closed claims

| Claim | Proof |
| --- | --- |
| `context_validity` | Induction on typing. |
| `weakening`, `substitution`, `type_correctness` | Nameless structural rules, typed encoding, and typed reflection. |
| `abort_typing`, `unroll_typing`, `row_code_typing`, `signature_typing` | Derived rules using the proved weakening theorem. |
| `list_definitions_well_typed`, `nil_typing`, `cons_typing`, `nonempty_cons_typing`, `reused_tree_cons_typing`, `nonempty_widening`, `nonempty_observers_typing` | Symbolic typing proofs using proved structural rules. |
| `conversion_joinability`, `confluence` | Parallel reduction with named/nameless encoding and reflection. |
| `progress` | All typing rules, using closed conversion joinability. |
| `canonical_forms_close` | Constructor inversion and injectivity of conversion at close types. |
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

## Other conditional claims

| Claim | Remaining assumptions |
| --- | --- |
| `close_induction_preservation`, `dead_sound` | `full_preservation` |
| `row_handlers_sound`, `description_subtyping_sound` | `full_preservation` |
| `subtyping_sound`, `case_handlers_sound`, `synthesis_sound`, `checking_sound` | `full_preservation` |
| `dead_close_uninhabited`, `canonical_forms_named`, `self_restricted_list_empty`, `close_roll_unroll`, `no_uniform_list_downcast` | `full_preservation`, `normalization` |

The downcast argument instantiates the alleged function at `Bot`, applies
it to the empty list, and uses the nonempty-list head observer and consistency.

## Counterexample to full preservation

Let `Gamma = f : Unit -> Sort 0`. The rules derive
`Gamma |- (lambda x. f x) : Unit -> Sort 1` by applying universe cumulativity
to `f x` inside the lambda. Unrestricted eta reduction removes the lambda,
producing `f`. The variable rule and conversion do not assign `f` the type
`Unit -> Sort 1`: conversion preserves the distinct codomain universe levels.

The counterexample's typing, reduction, and failure of reduct typing are all
proved without axioms. It imports no declarations from
`OpenSignaturesTheorems.v`. Consequently, proofs that still depend on
`full_preservation` do not establish soundness of the current calculus.

Fixing this requires a design decision. Cumulative function typing can
support eta contraction; removing eta requires revisiting both reduction
and conversion, because the existing conversion-joinability theorem also
uses eta reduction. The theorem statements and calculus have been preserved.

The auxiliary [beta/projection preservation proofs](nameless/DBBeta.v) and
[context conversion proof](nameless/DBContexts.v) are axiom-free; the failure
is exhibited specifically by unrestricted eta contraction with cumulativity.
[OpenSignaturesBeta.v](OpenSignaturesBeta.v) transports beta preservation to
the named calculus. [OpenSignaturesPayloadInversion.v](OpenSignaturesPayloadInversion.v)
recovers a close constructor's typed payload using injectivity of conversion.
These independent results close `closing_substitution` and `canonical_forms_close`.

## Remaining work

The four remaining conjecture declarations are `full_preservation`, `normalization`,
`coercion_coherence`, and `checking_coherence`. No new axioms or changed
theorem premises have been used to discharge claims. `full_preservation` is refuted above; the other three remain unproved.

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
make -C progress open-signatures check-bindings check-eta-counterexample audit-open-signatures
rocq check -silent -Q progress '' OpenSignaturesTheorems OpenSignaturesEtaCounterexample
```

The audit covers all 47 original claims and the supporting results. A
successful build does not eliminate printed assumptions. Section theorems
such as `progress_from_conversion` close over their explicit joinability
premise; the public `progress` theorem supplies the proved joinability theorem.
