(* Factor direct erased-sort reflection into a core reflection lemma and an
   endpoint-aware eta backward-conversion lemma. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep
  _parent_phi_erase_sort_algebra _parent_phi_erase_sort_direct.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Definition phi_erase_pstep_reflect_parent : Prop :=
  forall t u, pstep (phi_erase t) u ->
    exists t', pstep t t' /\ phi_erase t' = u.

Definition phi_erase_eta_step_sort_backward_parent : Prop :=
  forall t u j,
    epstep (phi_erase t) u -> conv u (TSort j) ->
    conv t (TSort j).

Lemma rtc_pstep_phi_erase_reflect_parent :
    phi_erase_pstep_reflect_parent ->
    forall t u, rtc pstep (phi_erase t) u ->
    exists t', rtc pstep t t' /\ phi_erase t' = u.
Proof.
  intros REF t u H.
  remember (phi_erase t) as x eqn:Hx. revert t Hx.
  induction H as [x | x y z Hxy Hyz IH]; intros t Hx.
  - exists t. split; [apply rtc_refl | symmetry; exact Hx].
  - assert (Hxy' : pstep (phi_erase t) y).
    { rewrite <- Hx. exact Hxy. }
    destruct (REF t y Hxy') as [t1 [Ht1 He1]].
    destruct (IH t1 (eq_sym He1)) as [t2 [Ht2 He2]].
    exists t2. split; [eapply rtc_step; eassumption | exact He2].
Qed.

Theorem phi_erase_sort_endpoint_from_factor_parent :
    phi_erase_pstep_reflect_parent ->
    phi_erase_eta_step_sort_backward_parent ->
    phi_erase_sort_endpoint_reflect_parent.
Proof.
  intros PREF EBACK t j Hred.
  remember (phi_erase t) as x eqn:Hx.
  remember (TSort j) as z eqn:Hz.
  revert t j Hx Hz.
  induction Hred as [x | x y z Hxy Hyz IH];
    intros t j Hx Hz.
  - assert (Hphi : phi_erase t = TSort j).
    { eapply eq_trans; [apply eq_sym; exact Hx | exact Hz]. }
    pose proof (phi_erase_sort_preimage_parent t j Hphi) as ->.
    rewrite Hz. apply cv_refl.
  - destruct Hxy as [s u Hcore | s u Heta].
    + rewrite Hx in Hcore.
      destruct (rtc_pstep_phi_erase_reflect_parent PREF t _ Hcore)
        as [t1 [Ht1 He1]].
      eapply cv_trans.
      * apply rtc_pstep_conv. exact Ht1.
      * eapply IH; [symmetry; exact He1 | exact Hz].
    + rewrite Hx in Heta.
      inversion Heta as [q0 | q0 r0 s0 Hfirst Htail]; subst.
      * eapply IH; reflexivity.
      * eapply EBACK; [exact Hfirst |].
        eapply cv_trans.
        -- apply rtc_epstep_conv. exact Htail.
        -- apply rtc_cstep_conv. exact Hyz.
Qed.

Print Assumptions rtc_pstep_phi_erase_reflect_parent.
Print Assumptions phi_erase_sort_endpoint_from_factor_parent.
