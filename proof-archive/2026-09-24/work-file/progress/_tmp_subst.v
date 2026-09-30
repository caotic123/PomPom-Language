Require Import TypeRules Progress.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Lemma try_pstep_subst :
  (forall t t' (H : pstep t t'), forall u u' k,
      pstep u u' -> pstep (subst u k t) (subst u' k t')) /\
  (forall bs bs' (H : pbranches bs bs'), forall u u' k,
      pstep u u' ->
      pbranches
        (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
        (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) bs')).
Proof.
  apply pstep_pbranches_ind; cbn; intros;
    try solve [constructor; eauto using pstep_refl, pstep_lift].
  - change (pstep (subst u k (TVar n)) (subst u' k (TVar n))).
    destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
    + assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
      cbn [subst]. rewrite Hlt. apply pstep_refl.
    + subst n.
      assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
      cbn [subst]. rewrite Hlt, Heq. eapply pstep_lift. exact H.
    + assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
      cbn [subst]. rewrite Hlt, Heq. apply pstep_refl.
  - rewrite subst_subst_zero_comm. eapply ps_beta; eauto.
  - eapply ps_fst_pair; eauto.
  - eapply ps_snd_pair; eauto.
  - eapply ps_epi_nil; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    repeat rewrite (subst_lift_one_one _ u' k).
    repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_epi_cons; eauto.
  - eapply ps_switch_zero; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_switch_succ; eauto.
  - eapply ps_interp_one; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_interp_prod; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_interp_pi; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_interp_sig; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_interp_choice; eauto.
  - eapply ps_iall_var; eauto.
  - eapply ps_iall_one; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_iall_prod; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_iall_pi; eauto.
  - eapply ps_iall_sig; eauto.
  - eapply ps_iall_choice; eauto.
  - eapply ps_hyps_var; eauto.
  - eapply ps_hyps_one; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_hyps_pi; eauto.
  - eapply ps_hyps_sig; eauto.
  - eapply ps_hyps_choice; eauto.
  - repeat rewrite (subst_lift_two_zero _ u' k).
    eapply ps_ind_red; eauto.
  - rewrite subst_subst_zero_comm.
    eapply ps_case_red with
      (k:=k) (c:=subst u k0 c) (b:=subst u (S k0) b) (n:=n).
    + eapply nth_error_subst_branches. exact e.
    + rewrite (enum_pos_subst_id c n e0 u k0). exact e0.
    + rewrite (enum_pos_subst_id a n e1 u k0). exact e1.
    + intros j cj bj Hj Hnth.
      rewrite nth_error_map in Hnth.
      destruct (nth_error bs j) as [[cj0 bj0]|] eqn:Horig;
        cbn in Hnth; [|discriminate].
      inversion Hnth; subst cj bj.
      destruct (e2 j cj0 bj0 Hj Horig) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite (enum_pos_subst_id cj0 nj Hpos u k0). exact Hpos.
      * exact Hneq.
    + eauto.
    + eauto.
Qed.
