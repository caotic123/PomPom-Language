# PomPom typing rules

Open [type-rules.pdf](type-rules.pdf) for the mathematical presentation, or
edit [type-rules.tex](type-rules.tex) and its three included `.tex` files.

The source formalization in this checkout is **Rocq/Coq**, not Lean. This
is a readable transcription of `progress/TypeRulesCore.v`, re-exported by
`progress/TypeRules.v`, with principal
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
The source layout is documented in [progress/README.md](../../progress/README.md).
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
