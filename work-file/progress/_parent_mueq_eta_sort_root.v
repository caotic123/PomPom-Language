(* Sort-ending eta simulation excludes the opaque TMuS exception. *)

Require Import Progress _tmp_epstep _work_mixed_closure
  _luna_mueq _glm_mueq_eta_shape _parent_mus_cstep_inv.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Theorem mueq_eta_root_sort_sim_parent :
    mueq_lift1_descent_glm ->
    forall f u j,
      mueq (TLam (TApp (lift 1 0 f) (TVar 0))) u ->
      rtc cstep f (TSort j) ->
      exists u', rtc epstep u u' /\ mueq f u'.
Proof.
  intros Hdescent f u j Hm Hsort.
  eapply mueq_eta_root_sim_rtc_from_lift_descent_glm;
    [exact Hdescent | exact Hm |].
  intros S1 Hhead.
  destruct (lift1_tmus_head_inv_glm f S1 Hhead) as [S0 Hf].
  subst f. exact (rtc_cstep_mus_not_sort_parent S0 j Hsort).
Qed.

Print Assumptions mueq_eta_root_sort_sim_parent.
