(* GLM worker 1 — cjoin-subst bundle, part 1: mutual pstep/pbranches
   substitution under the SAME arbitrary substituent. *)

Require Import Progress.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules.

Lemma pstep_var_subst_same_glm : forall n u k,
    pstep (subst u k (TVar n)) (subst u k (TVar n)).
Proof.
  intros n u k.
  destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
  - assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
    cbn [subst]. rewrite Hlt. apply pstep_refl.
  - subst n.
    assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
    cbn [subst]. rewrite Hlt, Heq. apply pstep_refl.
  - assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
    cbn [subst]. rewrite Hlt, Heq. apply pstep_refl.
Qed.

Lemma pstep_pbranches_subst_same_glm :
  (forall t t' (H : pstep t t'), forall u k,
      pstep (subst u k t) (subst u k t')) /\
  (forall bs bs' (H : pbranches bs bs'), forall u k,
      pbranches
        (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
        (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs')).
Proof.
  apply pstep_pbranches_ind; cbn; intros;
    try solve [constructor; eauto using pstep_refl, pstep_lift].
  - (* ps_var *)
    change (pstep (subst u k (TVar n)) (subst u k (TVar n))).
    apply pstep_var_subst_same_glm.
  - (* ps_beta *)
    rewrite subst_subst_zero_comm. eapply ps_beta; eauto.
  - (* ps_fst_pair *)
    eapply ps_fst_pair; eauto.
  - (* ps_snd_pair *)
    eapply ps_snd_pair; eauto.
  - (* ps_epi_nil *)
    eapply ps_epi_nil; eauto.
  - (* ps_epi_cons *)
    repeat rewrite (subst_lift_one_zero _ u k).
    repeat rewrite (subst_lift_one_one _ u k).
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply ps_epi_cons; eauto.
  - (* ps_switch_zero *)
    eapply ps_switch_zero; eauto.
  - (* ps_switch_succ *)
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply ps_switch_succ; eauto.
  - (* ps_interp_one *)
    eapply ps_interp_one; eauto.
  - (* ps_interp_prod *)
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply ps_interp_prod; eauto.
  - (* ps_interp_pi *)
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply ps_interp_pi; eauto.
  - (* ps_interp_sig *)
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply ps_interp_sig; eauto.
  - (* ps_interp_choice *)
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply ps_interp_choice; eauto.
  - (* ps_iall_var *)
    eapply ps_iall_var; eauto.
  - (* ps_iall_one *)
    eapply ps_iall_one; eauto.
  - (* ps_iall_prod *)
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply ps_iall_prod; eauto.
  - (* ps_iall_pi *)
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply ps_iall_pi; eauto.
  - (* ps_iall_sig *)
    eapply ps_iall_sig; eauto.
  - (* ps_iall_choice *)
    eapply ps_iall_choice; eauto.
  - (* ps_hyps_var *)
    eapply ps_hyps_var; eauto.
  - (* ps_hyps_one *)
    eapply ps_hyps_one; eauto.
  - (* ps_hyps_pi *)
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply ps_hyps_pi; eauto.
  - (* ps_hyps_sig *)
    eapply ps_hyps_sig; eauto.
  - (* ps_hyps_choice *)
    eapply ps_hyps_choice; eauto.
  - (* ps_ind_red *)
    repeat rewrite (subst_lift_two_zero _ u k).
    eapply ps_ind_red; eauto.
  - (* ps_case_red *)
    rewrite subst_subst_zero_comm.
    eapply ps_case_red with (k := k) (c := subst u k0 c)
                             (b := subst u (S k0) b) (n := n).
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

Corollary pstep_subst_same_glm : forall t t', pstep t t' -> forall u k,
    pstep (subst u k t) (subst u k t').
Proof. intros t t' H. exact (proj1 pstep_pbranches_subst_same_glm t t' H). Qed.

Corollary pbranches_subst_same_glm : forall bs bs', pbranches bs bs' ->
    forall u k,
    pbranches
      (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
      (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs').
Proof. intros bs bs' H. exact (proj2 pstep_pbranches_subst_same_glm bs bs' H). Qed.

Print Assumptions pstep_subst_same_glm.
Print Assumptions pbranches_subst_same_glm.
