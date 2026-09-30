# PomPom typing rules

## Open signatures and parameterized closure

The current rule reference is
[open-signatures.pdf](open-signatures.pdf), built from
[open-signatures.tex](open-signatures.tex) and its included files. It keeps
prose short while displaying all 82 context, typing, name-resolution, and
elaboration rules from the revised Rocq modules, with explicit formation
premises and searchable Rocq rule names. It includes structural computation
equations, concrete list/nonempty-list/tree instantiations, dependent function
coercions, and a bibliography. Selected theorem statements are explicitly
marked unproved, matching the
[OpenSignatures Rocq specification](../../progress/OpenSignatures.md).

| LaTeX source | Contents |
| --- | --- |
| [open-signatures-core.tex](open-signatures-core.tex) | Contexts, universes, Π/Σ, enumerations, descriptions, `iAll`, `hyps`, reference μᴵ, and `close`. |
| [open-signatures-elaboration.tex](open-signatures-elaboration.tex) | Rows, dead witnesses, row handlers, description/type coercions, source checking and synthesis, constructors, and cases. |
| [open-signatures-examples.tex](open-signatures-examples.tex) | Lists, nonempty lists, constructor reuse, compact/padded conversions, observers, and instantiated induction hypotheses. |
| [open-signatures-theorems.tex](open-signatures-theorems.tex) | Selected unproved theorem statements and the source map. |
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
