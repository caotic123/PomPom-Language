# Proof work files

This directory preserves the exploratory Coq developments that were formerly
named `_tmp_*` in `progress/`. The main sources live in `work-file/progress/`;
generated `.aux`, `.glob`, `.vo`, `.vok`, and `.vos` files were preserved too,
but source plus a fresh `coqc` run is authoritative.

The scratch modules import the live `progress/Progress.v` and often import one
another by their `_tmp_*` logical names. A typical one-file check is:

```sh
cd work-file/progress
coqc -Q ../../progress '' _tmp_epstep.v
```

For a dependent module, compile its imported scratch modules first in the
same directory. Existing `.vo` files may be stale after edits to
`progress/Progress.v`.

## Trusted milestones

The most useful completed source files are:

- `_tmp_pdev_lift.v`
- `_tmp_eta_cancel.v`
- `_tmp_eta_shape.v`
- `_tmp_epstep.v`
- `_tmp_epstep_inv.v`
- `_tmp_eta_tool.v`
- `_tmp_epstep_diamond.v`
- `_tmp_epstep_subst.v`
- `_tmp_epbranches_nth.v`
- `_tmp_pstep_var_rigid.v`
- `ProgressWork.v` (stable aggregate of every completed work module)
- `_work_commute.v`
- `_work_mixed_closure.v`
- `_work_cjoin.v`
- `_work_cstep_invariants.v`
- `_work_conv_whd_pos.v`

Their dependencies include `_tmp_lower.v`, `_tmp_case_lift.v`,
`_tmp_epi_helper.v`, `_tmp_ind_helper.v`, `_tmp_switch_full.v`,
`_tmp_iall_full.v`, and `_tmp_hyps_full.v`.

## Do not treat as completed

- `_tmp_lower.v` aborts `lower_sound_aux` near the end; earlier declarations
  in the module are usable.
- `_tmp_convpos.v` assumes `conv_join` with `Parameter`.
- `_tmp_eqdec.v`, `_tmp_subst_var.v`, and `_tmp_dbg.v` contain aborted
  experiments.
- `_tmp_convfinal.v` is a failed direct approach, not a proof.
- `_work_commute_eta_ind.v` is an abandoned direct induction and contains an
  `Abort`; use `_work_commute.v` instead.

Use `rg -n '\b(Abort|Admitted|Parameter|Axiom|Conjecture)\b' *.v` before
promoting any scratch module into `Progress.v`.
