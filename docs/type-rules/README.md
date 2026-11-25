# PomPom typing rules

An [explicitly annotated core repair](../../progress/annotated/README.md)
follows the September 30 design decision. Full preservation is proved for that
core without axioms, but its strong normalization is open. On October 11 the
user decided to keep the public calculus unannotated, so the PDF below
documents the existing named calculus, its checked counterexample, and the
status of the repair.

## Condensed reference

[calculus.pdf](calculus.pdf), built from the single file
[calculus.tex](calculus.tex), states the current open-signature calculus in
two parts. Part I is the core, presented as an extension of the type theory
of Dagand and McBride, *Elaborating Inductive Definitions*
([arXiv:1210.6390](https://arxiv.org/abs/1210.6390)): the rules that come
from that paper are written in its notation, grouped as in its Figures 1, 2
and 4, and cited; every rule that is ours or departs from the paper's is
marked with a dagger and explained (explicit universe levels and
cumulativity, the empty code, induction-hypothesis computation, and
parameterized closure). Each operator's computation rules sit beside its
typing rules, followed by reduction and conversion, observational
equivalence, and the core metatheory. Part II is elaboration: rows,
dead branches, coercions, source checking, and its soundness and coherence
theorems. Each part lists its supporting lemmas and proof structure. Start
here; the longer document below adds instantiations and citations. Build it
with `make -C docs/type-rules calculus`.

The document is checked against the Rocq sources. Its rules, definitions,
theorem statements, and examples are restated in
[OpenSignaturesDocCheckCore.v](../../progress/OpenSignaturesDocCheckCore.v),
[OpenSignaturesDocCheckElab.v](../../progress/OpenSignaturesDocCheckElab.v), and
[OpenSignaturesDocCheckRel.v](../../progress/OpenSignaturesDocCheckRel.v), each
proved from the constructor or theorem it cites. After building the proof
library, run `make -C docs/type-rules check`; a statement that no longer
matches the sources fails to compile. When a rule changes, update the
document and its restatement together.

## Open signatures and parameterized closure

**Outdated since 2026-11-25.** This longer document predates the
restriction of row coercions to a shared label set: it still shows
`ds_rows` without the equal-names premise and a `NonEmpty` that drops the
`nil` label. Use the condensed reference above for the current rules.

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

Forty-six original claims have proofs without axiom dependencies, including
coercion and checking coherence, and full preservation is refuted. No
conjectures remain. The PDF and its
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
coherence claims are proved through a binary relational model. Full beta/eta strong normalization
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
