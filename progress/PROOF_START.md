# First theorem: context validity

Status: **proved**. The first of 47 statements in
[OpenSignaturesTheorems.v](OpenSignaturesTheorems.v) has a checked proof
with no axiom dependencies. The complete development now has forty-four closed
claims, two coherence conjectures, and one refuted claim; no proved claims
depend on conjectures;
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

The audit binds `context_validity` in its collection of closed proofs and
checks them together with `Print Assumptions audited_closed_proofs.` That
command must report `Closed under the global context`; this covers every
proof in the collection, including `context_validity`. A successful build alone is insufficient.
Use no `Admitted`, added axiom, or conditional theorem premise to close it.

The principal elaboration and subtyping soundness results are now proved without
axioms. Full beta/eta `normalization` is proved. Full preservation is refuted;
the two coherence claims remain open. `weakening`, `substitution`, and
`type_correctness` are proved.
See the dependency table in `PROOF_STATUS.md`.

Function cumulativity repairs the earlier universe-variance counterexamples.
A separate [polymorphic application counterexample](OpenSignaturesEtaPolymorphism.v)
refutes unrestricted eta preservation in the current rules. See the axiom-free [regressions](OpenSignaturesEtaRegression.v), the [updated rules](type-rules.md), and [remaining proof obligations](PROOF_STATUS.md).
