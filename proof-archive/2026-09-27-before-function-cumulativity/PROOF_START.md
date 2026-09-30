# First theorem: context validity

Status: **proved**. The first of 47 statements in
[OpenSignaturesTheorems.v](OpenSignaturesTheorems.v) has a checked proof
with no axiom dependencies. The complete development now has twenty-seven closed
claims, 16 derived claims depending on conjectures, and 4 conjectures;
see [PROOF_STATUS.md](PROOF_STATUS.md). The first theorem is:

```coq
Theorem context_validity :
  forall Gamma t A, typing Gamma t A -> wf Gamma.
```

This says that every typing derivation uses a well-formed context. It says
nothing yet about whether the type `A` is itself well-formed; that is the
next theorem, `type_correctness`.

## Where to work

Read the mutually defined `wf` and `typing` judgments in
[OpenSignaturesCore.v](OpenSignaturesCore.v). The proof in
[OpenSignaturesTheorems.v](OpenSignaturesTheorems.v) uses
`induction Htyping; assumption.` and closes with a checked `Qed`.

Use the core rules and standard-library reasoning. Keep the statement and
typing rules unchanged, and do not use any of the remaining conjectures or
import archived proofs.

## Starting approach

Induct on the typing derivation, generalizing over its context, term, and
type. For constructors such as `ty_var`, `ty_sort`, and `ty_unit`, the
required `wf Gamma` is already a premise. For the other constructors, use
the induction hypothesis for a typing premise in the same context `Gamma`.
Binder rules also carry a formation premise in `Gamma`; inspect that premise
before using an induction hypothesis about an extended context.

This target should require no substitution, preservation, conversion, or
progress results.

## Acceptance check

From the repository root:

```sh
make -C progress open-signatures
make -C progress audit-open-signatures
```

These commands now succeed. The unfinished weakening and type-correctness
attempts are preserved in
[the archive](../proof-archive/2026-09-26/OpenSignaturesTheorems.partial.v),
and their replacements are now proved without axioms. Use
`make -C progress check-bindings` to check the binding regressions separately.

The audit includes `Print Assumptions context_validity.` Its output
must report `Closed under the global context`, with no axioms listed for
this theorem. A successful build alone is insufficient.
Use no `Admitted`, added axiom, or conditional theorem premise to close it.

The remaining prerequisites for the principal soundness results are
`full_preservation` and `normalization`; the former is refuted under the current
rules. `weakening`, `substitution`, and `type_correctness` are proved.
See the dependency table in `PROOF_STATUS.md`.

The current unrestricted eta rule makes `full_preservation` false. See the axiom-free [counterexample](OpenSignaturesEtaCounterexample.v) and [proof status](PROOF_STATUS.md).
