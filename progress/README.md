# Rocq specifications — stable numeric bindings

The user selected an [annotated core repair](annotated/README.md) on September
30 to recover full preservation while retaining general eta contraction.
It is under construction and checked with `make -C progress annotated-core
audit-annotated-core`; the public calculus and counts below have not yet been
migrated.

**Theorem 1: `context_validity` is proved** in
[OpenSignaturesTheorems.v](OpenSignaturesTheorems.v).
The [first-proof guide](PROOF_START.md) gives its meaning, proof approach,
and acceptance check.

```coq
forall Gamma t A, typing Gamma t A -> wf Gamma.
```

The active development uses stable numeric binding IDs, finite-map contexts,
capture-avoiding substitution, and an alpha-equivalence setoid. Terms can be
interned with consecutive numeric IDs; alpha-equivalent terms share an ID
within the same table. There is no hashing. See [STABLE_IDS.md](STABLE_IDS.md).

Of the **47 original metatheory statements**, forty-four have proofs with no
axiom dependencies, two coherence claims remain conjectures, and full
preservation is refuted. No proved claims depend on conjectures. See [PROOF_STATUS.md](PROOF_STATUS.md) for the exact dependencies.
Progress, conversion joinability, confluence, and label uniqueness now have
proofs without axiom dependencies. Operational preservation, evaluation
preservation, and close-induction preservation are now also proved independently. Weakening, type correctness, substitution, closing substitution,
and canonical forms for close values are also proved without axioms.
Dead-witness, handler, subtyping, synthesis, and checking soundness are proved
without axioms, using typed computation/eta factorization.
Full beta/eta strong normalization is proved for every typing derivation.
The semantic model covers cumulative universes, descriptions, positive fixed
points, closure, and all primitive operators. The fundamental theorem and
substitution reflection transfer normalization to the original named calculus.
Consistency and all six previously conditional claims are now closed.
[Full preservation is refuted](OpenSignaturesEtaPolymorphism.v); both
coherence claims remain open. The confluence proof
adapts the archived parallel-reduction method and proves its connection to
named terms.

Check the implemented modules, binding regressions, and example computations:

```sh
make -C progress check-bindings
```

The full build now succeeds. The original unfinished weakening and type
correctness attempts are preserved in
[the September 26 archive](../proof-archive/2026-09-26/OpenSignaturesTheorems.partial.v);
their replacements are now proved without axioms.

```sh
make -C progress open-signatures
make -C progress audit-open-signatures
```

The audit checks the proved claims, the two open claims, and the independent
refutation of full preservation. It checks all closed dependencies in one
collection and prints the two open coherence assumptions separately. Compiling a
conjecture, or a theorem depending on one, does not discharge that assumption.

See [OpenSignatures.md](OpenSignatures.md) for the module map and
[type-rules.md](type-rules.md) for the mathematical rules.

All prior proof work is saved in
[proof-archive/2026-09-24](../proof-archive/2026-09-24/README.md): the earlier
calculus, scratch developments, unfinished open-signature progress proof,
ten computation proofs, and generated Rocq artifacts. The archive is
excluded from the active build. The former `open-signatures-progress`
target has been removed.

Function cumulativity repairs the earlier universe-variance counterexamples,
but a [polymorphic application counterexample](OpenSignaturesEtaPolymorphism.v)
refutes unrestricted eta preservation in the current rules. See the axiom-free [regressions](OpenSignaturesEtaRegression.v), the [updated rules](type-rules.md), and [remaining proof obligations](PROOF_STATUS.md).
