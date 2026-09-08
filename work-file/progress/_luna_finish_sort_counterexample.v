Require Import Progress _tmp_epstep _work_cjoin _work_cstep_invariants
  _work_mixed_closure _parent_phi_erase_sort_factor _parent_phi_erase_sort_direct
  _parent_finish_branch_sound _luna_finish_branch_rigid
  _luna_finish_branch_erase _luna_finish_eta_sort.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma bad_not_conv_sort : forall j, ~ conv bad_t (TSort j).
Proof.
  intros j Hc.
  pose proof (branch_erase_conv bad_t (TSort j) Hc) as Hfc.
  destruct (fconv_cjoin _ _ Hfc) as [w [Hw1 Hw2]].
  pose proof (branch_bad_rtc_cstep_id w Hw1) as Hw.
  subst w.
  cbn [branch_erase] in Hw2.
  pose proof (rtc_cstep_sort_id _ _ Hw2) as Heq.
  rewrite branch_bad_def in Heq.
  discriminate Heq.
Qed.

Lemma bad_erased_sort_path : rtc cstep (phi_erase bad_t) (TSort 0).
Proof.
  eapply rtc_step.
  - apply epstep_cstep. exact bad_ep.
  - eapply rtc_step.
    + apply pstep_cstep. exact bad_u_sort.
    + apply rtc_refl.
Qed.

Theorem phi_erase_sort_endpoint_not_reflectable :
    ~ phi_erase_sort_endpoint_reflect_parent.
Proof.
  intro H.
  pose proof (H bad_t 0 bad_erased_sort_path) as Hbad.
  exact (bad_not_conv_sort 0 Hbad).
Qed.

Print Assumptions bad_not_conv_sort.
Print Assumptions bad_erased_sort_path.
Print Assumptions phi_erase_sort_endpoint_not_reflectable.
