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

(** Closed replacements and narrowed consumers for the remaining local
    assumptions in [Progress.v]. *)
Require Export _glm_enumt_cons_nil.
Require Export _glm_conv_subst0.
Require Export _parent_conv_subst_all.
Require Export _glm_muapp_sort_from_pi.
Require Export _parent_phi_erase_sort_algebra.
Require Export _parent_check_pi_formation.
Require Export _parent_mus_cstep_inv.
Require Export _parent_inert_cstep_inv.
Require Export _parent_epi_nonsort.
Require Export _parent_cstep_standardize_counterexample.
Require Export _parent_mueq_eta_sort_root.
Require Export _parent_mueq_eta_sort_recursive.
Require Export _parent_mueq_sort_stable.
Require Export _parent_mueq_projection_sort_recursive.
Require Export _parent_mueq_interp_sort_recursive.
Require Export _parent_pi_sort_rep_consumer.
Require Export _parent_pi_sort_rep_normalize.
Require Export _parent_mueq_pi_hshape_recursive.
Require Export _parent_muapp_sort_from_endpoint.
Require Export _parent_phi_erase_sort_direct.
Require Export _parent_phi_erase_sort_hshape.
Require Export _parent_phi_erase_idem.
Require Export _parent_phi_erase_epstep_forward.
Require Export _parent_phi_erase_sort_factor.
Require Export _parent_phi_erase_fixed_sort.
Require Export _parent_muapp_sort_from_pi_sort.
Require Export _glm_phi_erase_sort_pipeline.

(** Checked boundary of the erasure-reflection approach: unrestricted eta
    reflection is false, so later work must use a sort-ending invariant. *)
Require Export _glm_phi_erase_epstep_counterexample.
