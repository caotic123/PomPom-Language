# Coq metatheory

The formalization in this directory is Rocq/Coq. `TypeRulesCore.v` contains
the language, typing, conversion, subtyping, value, and `Bot` definitions.
`TypeRules.v` is the public entry point and re-exports the core and theorem
modules. `Require Import TypeRules` keeps the unqualified names available.
Fully qualified names now use their owning modules, for example
`TypeRulesCore.term`, `Progress.progress`, and `Preservation.preservation`.

The main metatheory is split by result:

- `Progress.v` contains the closed progress development and
  both `progress` and `progress_proved`.
- `Preservation.v` contains the preservation statement, which remains a
  conjecture.
- `PreservationEval.v` contains the corollary depending on preservation.
- `PreservationType.v` is closed.
- `Normalization.v`, `CanonicalFormsSig.v`, `Consistency.v`,
  `ConsistencyEnum.v`, `ConsistencyEmptySig.v`, and `AgainstSound.v` retain
  their exact remaining conjectures.

Seven conjectures therefore remain: preservation, normalization, canonical
forms for signatures, consistency, enum consistency, empty-signature
consistency, and against-soundness. No newly proved result is claimed by this
layout split. Existing scratch libraries may need their imports rebuilt or
updated to use `TypeRulesCore.v`.

Build and audit the formalization with:

```sh
make -C progress
make -C progress audit
```

Proof modules should import `TypeRulesCore`, rather than the `TypeRules`
entry point, to avoid circular imports as more obligations are proved.
The build lists active sources explicitly; historical copies and files under
`work-file/` are not included.
