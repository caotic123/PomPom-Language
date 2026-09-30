# Proof archive — 2026-09-24 restart

This folder preserves the proof work removed from the active development
when restarting from `context_validity`. Nothing here is imported or built
by the active `progress/Makefile` or `progress/_CoqProject`.

Paths beneath this folder mirror their locations before the restart:

| Saved path | Contents |
| --- | --- |
| `progress/_old/` | Earlier signature-pair calculus, proof sources, and generated files. |
| `work-file/` | All scratch proof developments, generated files, and their historical README. |
| `progress/OpenSignaturesProgress.v` | Unfinished progress proof for the revised calculus. Its last verification was interrupted while checking `pstep_complete`; it is not a completed progress proof. |
| `progress/OpenSignaturesExamples.v` | Original example definitions and all ten computation proofs. |
| Other `progress/` files | Original revised-calculus sources, theorem declarations, audit, build configuration, documentation, and generated Rocq artifacts. |
| `.lia.cache` | Saved repository-root arithmetic tactic cache. |
| `docs/type-rules/README.md` | Documentation before the restart. |

Historical documentation describes the old layout and status. Compiled
objects may be stale or tied to old load paths; their presence does not
certify a proof. Restore needed sources into a separate working directory
and rebuild their dependencies before reusing them. The current theorem
statements and proof status live in [progress/README.md](../../progress/README.md).

The first active target and its acceptance criteria are documented in
[PROOF_START.md](../../progress/PROOF_START.md).
