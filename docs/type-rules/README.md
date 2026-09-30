# PomPom typing rules

An [explicitly annotated core repair](../../progress/annotated/README.md) is
under construction following the September 30 design decision. The PDF below
still documents the existing named calculus and its checked counterexample;
it will be migrated when the annotated preservation proof is complete.

## Open signatures and parameterized closure

The current rule reference is
[open-signatures.pdf](open-signatures.pdf), built from
[open-signatures.tex](open-signatures.tex) and its included files. It keeps
prose short while displaying the current context, typing, name-resolution,
and elaboration rules, with explicit formation premises and searchable Rocq
rule names. Function cumulativity is contravariant in domains and covariant
in codomains, recursively through dependent functions; both function types
must be well formed. The reference includes the eta regression examples,
structural computation equations, concrete list/nonempty-list/tree
instantiations, dependent function coercions, and a bibliography.

Forty-four original claims have proofs without axiom dependencies, two
coherence claims remain conjectures, and full preservation is refuted. No proved claims depend on conjectures. The PDF and its
LaTeX sources distinguish these statuses; see the
[current proof status](../../progress/PROOF_STATUS.md) for exact dependencies.
Named binders use [stable numeric IDs and an alpha setoid](../../progress/STABLE_IDS.md).
The archived eta counterexample concerns the
[pre-repair rules](../../proof-archive/2026-09-27-before-function-cumulativity/README.md).
The active [regressions](../../progress/OpenSignaturesEtaRegression.v) check
both function variance directions and a nested dependent function, without
assuming full preservation. Execution preservation and elaboration soundness
are proved. Typed computation/eta factorization removes the earlier
full-preservation dependency from description views. The separate
[polymorphic application counterexample](../../progress/OpenSignaturesEtaPolymorphism.v)
refutes full preservation even with function cumulativity. Its false axiom
was removed, with the exact proposition retained for reference. The two
coherence claims remain open. Full beta/eta strong normalization
is proved for every typing derivation, using the cumulative semantic model,
positive fixed points, computability of every primitive operator, and the
full fundamental typing theorem. Semantic environments and substitution
reflection transfer the result to the original named calculus. Consistency
and all six formerly conditional claims are now closed without assumptions.
The current source snapshot is recorded in
[open-signatures-source-sha256.txt](open-signatures-source-sha256.txt).

| LaTeX source | Contents |
| --- | --- |
| [open-signatures-core.tex](open-signatures-core.tex) | Contexts, universes, Π/Σ, enumerations, descriptions, `iAll`, `hyps`, reference μᴵ, and `close`. |
| [open-signatures-elaboration.tex](open-signatures-elaboration.tex) | Rows, dead witnesses, row handlers, description/type coercions, source checking and synthesis, constructors, and cases. |
| [open-signatures-examples.tex](open-signatures-examples.tex) | Lists, nonempty lists, constructor reuse, compact/padded conversions, observers, and instantiated induction hypotheses. |
| [open-signatures-theorems.tex](open-signatures-theorems.tex) | Selected theorem statements, current proof status, and the source map. |
| [open-signatures-references.tex](open-signatures-references.tex) | Paper citations and attribution of inherited constructions versus proposed rules. |

Build just this document from the repository root:

```sh
make -C docs/type-rules open-signatures
```

The default `make -C docs/type-rules` builds both documents. Both use
`latexmk` and pdfLaTeX; `make -C docs/type-rules clean` removes auxiliary
files while retaining the PDFs.

## Earlier signature-pair calculus

Open [type-rules.pdf](type-rules.pdf) for the mathematical presentation, or
edit [type-rules.tex](type-rules.tex) and its three included `.tex` files.

The source formalization in this checkout is **Rocq/Coq**, not Lean. This
is a readable transcription of the archived `TypeRulesCore.v`, re-exported by
`TypeRules.v`, now under
[`proof-archive/2026-09-24/progress/_old/`](../../proof-archive/2026-09-24/progress/_old/), with principal
theorem statements from the integrated proof modules. It uses named
binders in place of de Bruijn indices and explicitly distinguishes
proved results, conditional theorems, and conjectures.

Rebuild from the repository root:

```sh
make -C docs/type-rules
```

Requires `latexmk`, pdfLaTeX, and the standard TeX Live packages used in
the preamble (including `mathpartir` and `stmaryrd`). To remove auxiliary
files while retaining the PDF, run `make -C docs/type-rules clean`.

The PDF describes a snapshot from before the module split. Its theorem-status
notes and source paths may lag the current Coq files; use the proof README
linked below for current status. Rule labels
and source notes connect the notation to the corresponding Coq
constructors and declarations. `source-sha256.txt` identifies the exact
formalization files used for this snapshot.

Validation: the PDF compiled with no LaTeX layout or reference warnings;
sample rule and theorem pages were inspected visually. All 56 typing,
context, subtyping, and branch constructors are represented (the two
branch-list constructors are expressed as per-clause premises).
The following status concerns only that archived calculus.
The active source layout is documented in [progress/README.md](../../progress/README.md).
`Progress.v` contains closed `progress_proved`; `Preservation.v` retains the
preservation conjecture, while `PreservationEval.v` is its dependent
corollary. `PreservationType.v` is closed. `Normalization.v`,
`CanonicalFormsSig.v`, `Consistency.v`, `ConsistencyEnum.v`,
`ConsistencyEmptySig.v`, and `AgainstSound.v` retain their exact conjectures.
Seven conjectures remain in total; this documentation update makes no claim
that any of them has been newly proved. Existing scratch libraries may need
their imports rebuilt or updated to use `TypeRulesCore.v`.

`Print Assumptions` remains the validation mechanism for closed results, and
the transport-to-progress implication has an explicit transport premise.
The PDF validation above concerns that historical document, not the current
Coq module build.
