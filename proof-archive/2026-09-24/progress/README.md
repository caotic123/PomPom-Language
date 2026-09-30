# Rocq specifications

## Revised open-signature calculus

The new version of [type-rules.md](type-rules.md) is exported by
[OpenSignatures.v](OpenSignatures.v). It includes the `close F G` rules,
reusable constructor schemes, explicit coercion elaboration, and concrete
list examples. Its 47 metatheory statements are unproved conjectures; ten
closed computation checks are proved independently of them.

```sh
make -C progress open-signatures
make -C progress audit-open-signatures
make -C progress open-signatures-progress
```

See [OpenSignatures.md](OpenSignatures.md) for the module map, source-language
boundary, and theorem status.

`open-signatures-progress` additionally builds the work-in-progress progress
proof. Its generic relation-closure lemmas are defined locally, so it does not
depend on the earlier calculus.

## Archived signature-pair calculus

The earlier signature-pair modules are stored under [`_old/`](_old/). They are
kept for reference and are no longer part of `_CoqProject` or the active
Makefile.

The archived metatheory is split by result:

- [`_old/Progress.v`](_old/Progress.v) contains the closed progress development and
  both `progress` and `progress_proved`.
- [`_old/Preservation.v`](_old/Preservation.v) contains the preservation statement, which remains a
  conjecture.
- `_old/PreservationEval.v` contains the corollary depending on preservation.
- `_old/PreservationType.v` is closed.
- `_old/Normalization.v`, `_old/CanonicalFormsSig.v`, `_old/Consistency.v`,
  `_old/ConsistencyEnum.v`, `_old/ConsistencyEmptySig.v`, and
  `_old/AgainstSound.v` retain their exact remaining conjectures.

Seven conjectures therefore remain: preservation, normalization, canonical
forms for signatures, consistency, enum consistency, empty-signature
consistency, and against-soundness. No newly proved result is claimed by this
layout split. Existing scratch libraries may need their imports rebuilt or
their load paths adjusted if rebuilt from the archive.

The archive is intentionally not built by the active targets.
