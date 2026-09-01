(** Stable entry point for the proof developments that are not yet integrated
    into [progress/Progress.v].  Only completed declarations are re-exported
    here. *)

Require Export Progress.

(** Complete development commutes with lifting. *)
Require Export _tmp_pdev_lift.

(** Parallel eta reduction and its checked metatheory. *)
Require Export _tmp_epstep.
Require Export _tmp_eta_cancel.
Require Export _tmp_eta_shape.
Require Export _tmp_epstep_inv.
Require Export _tmp_eta_tool.
Require Export _tmp_epstep_subst.
Require Export _tmp_epstep_diamond.
Require Export _tmp_epbranches_nth.

(** Small rigidity helper and the persistent eta-fold abstraction. *)
Require Export _tmp_pstep_var_rigid.
Require Export _luna_eta_kfold.
Require Export _luna_eta_kfold_pstep.
Require Export _luna_enum_pos_lift_inv.
Require Export _luna_rtc_epbranches_nth.
Require Export _luna_fstep_split.
Require Export _luna_phi_erase_shapes.
Require Export _luna_parallel_hshape.
Require Export _luna_conv_enumt_observe.
Require Export _luna_pstep_rtc.
Require Export _work_pstep_lift_inv.
Require Export _work_eta_critical.
Require Export _work_epstep_rtc.
Require Export _work_commute.
Require Export _work_mixed_closure.
Require Export _work_cjoin.
Require Export _work_cstep_invariants.
Require Export _work_conv_whd_pos.
