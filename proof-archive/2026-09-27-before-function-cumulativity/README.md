# Before function cumulativity (2026-09-27)

This snapshot preserves the calculus and proof sources immediately before
adding `universe_le` and `ty_cumul_fun`. Its `OpenSignaturesEtaCounterexample.v`
contains the axiom-free negation of full preservation for those earlier rules.

The active calculus and regression checks are under `progress/`. The archived
counterexample does not apply to the repaired typing judgment. No archive
module is imported by the active proof build.
