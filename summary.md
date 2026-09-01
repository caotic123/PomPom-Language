# `Progress.v` proof status

State as of 2026-08-31. The goal is to replace only the four local
`Conjecture`s in `progress/Progress.v` with kernel-checked proofs, without
adding axioms.

## Current local assumptions

`progress/Progress.v` still contains exactly these four conjectures:

- `conv_whd`
- `conv_enumt_inj`
- `conv_pos`
- `muapp_sort`

`spine_covered`, which was previously a conjecture, is now proved.

## Integrated and checked infrastructure

The working `Progress.v` contains the following proof infrastructure:

- term-size induction and `tsize_lift`;
- de Bruijn lift/substitution algebra, including `subst_lift_cancel`;
- `phi_erase` and its compatibility lemmas;
- the full contextual relation `fstep`;
- the eta-free parallel computation relation `pstep`;
- complete development `pdev`;
- diamond and confluence for `pstep`;
- conversion soundness for `pstep` and the `pjoin` library;
- `spine_mem_covers_join` and the proved `spine_covered` lemma.

The main file still compiles with the four declarations above present.  The
new proofs below are intentionally staged in `work-file/progress/` until the
remaining two obligations are solved and the dependency block can be moved
into `Progress.v` in one controlled integration.

## Reusable scratch work

All prior scratch sources and their generated Coq artifacts were moved under
`work-file/progress/`. They are intentionally kept separate from the main
file while the eta/confluence architecture is being completed. See
`work-file/README.md` for the dependency and verification notes.

Important checked milestones include:

- `_tmp_pdev_lift.v`: `try_pdev_lift`;
- `_tmp_eta_cancel.v`: eta/beta substitution cancellation;
- `_tmp_eta_shape.v`: lowering/lifting and eta-shape decomposition;
- `_tmp_epstep.v`: parallel eta reduction and lift compatibility;
- `_tmp_epstep_inv.v`: generalized eta-step lift inversion;
- `_tmp_eta_tool.v`: eta application inversion;
- `_tmp_epstep_diamond.v`: diamond for parallel eta reduction;
- `_tmp_epstep_subst.v`: substitution compatibility for parallel eta;
- `_tmp_epbranches_nth.v`: branch lookup preservation;
- `_tmp_pstep_var_rigid.v`: variable rigidity for `pstep`.

The completed mixed-reduction development is re-exported by
`work-file/progress/ProgressWork.v` and includes:

- `_work_pstep_lift_inv.v`: inversion of a `pstep` whose source is lifted;
- `_work_eta_critical.v`: the nested lambda/beta/eta critical pair;
- `_work_epstep_rtc.v`: congruence, substitution, and branch lifting for
  reflexive-transitive eta reduction;
- `_work_commute.v`: stable entry point for the completed theorem
  `pstep_epstep_commute`;
- `_work_mixed_closure.v`: commutation of whole core/eta blocks and diamond
  plus confluence of the combined phase relation `cstep`;
- `_work_cjoin.v`: conversion-after-phi-erasure maps to `cstep` joins;
- `_work_cstep_invariants.v`: weak-head shape, `EnumT`, and canonical-position
  invariants for combined paths;
- `_work_conv_whd_pos.v`: closed, assumption-free proofs
  `conv_whd_proved` and `conv_pos_proved`.

The key correction is that one parallel eta step on the join's left side is
too strong for nested eta shells.  The valid commutation theorem has
`rtc epstep` there.  Treating whole core and eta closures as individual
phases then yields an ordinary diamond.

Small helper lemmas were delegated to Luna as requested; the complex
commutation/confluence architecture remains with the primary proof effort.

## Incomplete or untrusted scratch files

These files compile only because the named declaration is aborted or assumed;
they must not be cited as finished proofs:

- `_tmp_lower.v`: `lower_sound_aux` ends in `Abort`; the earlier lowering
  lemmas in that file are still available.
- `_tmp_convpos.v`: declares `conv_join` as a `Parameter`.
- `_tmp_eqdec.v` and `_tmp_subst_var.v`: contain aborted experiments.
- `_tmp_dbg.v`: is diagnostic and intentionally aborts.
- `_work_commute_eta_ind.v` and `_tmp_convfinal.v` are unsuccessful direct
  proof attempts; the latter's proposed
  `step_enum_pos_stable` statement is false (a projection may reduce to an
  enum position).

## Remaining proof obligations

Two exact declarations remain:

1. `conv_enumt_inj`.  Erased confluence proves all outer-shape consequences,
   but `phi_erase` deliberately forgets bare `TMuS` parameters, so equality
   of erased common reducts alone cannot reconstruct the required inner
   *original* conversion.  The remaining argument must be confluence modulo
   the contextual `cv_phi` equations (or an equivalent proof-normalization
   result), not an unsound reflection of `phi_erase`.
2. `muapp_sort`.  The synthesis-only case is already proved in `Progress.v`.
   The general checking case additionally needs conversion/subtyping
   injectivity for the Pi codomain, so it follows after the same
   confluence-modulo-phi layer used for `conv_enumt_inj`.

After those proofs, rename `conv_whd_proved`/`conv_pos_proved` to the original
declarations during integration, move the checked dependency block before
their use, and run the full audit below.

## Final verification

Run from `progress/`:

```sh
coqc -q TypeRules.v
coqc -q Progress.v
rg -n '^(Axiom|Conjecture)|Admitted|admit' Progress.v
```

Then audit the final theorem in Coq:

```coq
Require Import Progress.
Print Assumptions progress_proved.
```

The final audit may retain assumptions imported from `TypeRules.v` (notably
the externally supplied canonical-forms signature), but must contain none of
the four local conjectures listed above.
