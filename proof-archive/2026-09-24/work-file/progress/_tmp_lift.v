Require Import TypeRules Progress.
From Stdlib Require Import List.
Import ListNotations.

Lemma pstep_lift_mut :
  (forall t u (H:pstep t u), forall d k,
      pstep (lift d k t) (lift d k u)) /\
  (forall bs bs' (H:pbranches bs bs'), forall d k,
      pbranches
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs')).
Proof.
  apply pstep_pbranches_ind; cbn; intros;
    try solve [constructor; eauto using pstep_refl].
  - apply pstep_refl.
  - rewrite lift_subst_zero_comm. eapply ps_beta; eauto.
  - eapply ps_fst_pair; eauto.
  - eapply ps_snd_pair; eauto.
  - eapply ps_epi_nil; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    repeat rewrite (lift_lift_one_one _ d k).
    repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_epi_cons; eauto.
  - eapply ps_switch_zero; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_switch_succ; eauto.
  - eapply ps_interp_one; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_interp_prod; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_interp_pi; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_interp_sig; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_interp_choice; eauto.
  - eapply ps_iall_var; eauto.
  - eapply ps_iall_one; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_iall_prod; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_iall_pi; eauto.
  - eapply ps_iall_sig; eauto.
  - eapply ps_iall_choice; eauto.
  - eapply ps_hyps_var; eauto.
  - eapply ps_hyps_one; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_hyps_pi; eauto.
  - eapply ps_hyps_sig; eauto.
  - eapply ps_hyps_choice; eauto.
  - repeat rewrite (lift_lift_two_zero _ d k).
    eapply ps_ind_red; eauto.
  - rewrite lift_subst_zero_comm.
    eapply ps_case_red with
      (k:=k) (c:=lift d k0 c) (b:=lift d (S k0) b) (n:=n).
    + eapply nth_error_lift_branches. exact e.
    + rewrite (enum_pos_lift_id c n e0 d k0). exact e0.
    + rewrite (enum_pos_lift_id a n e1 d k0). exact e1.
    + intros j cj bj Hj Hnth.
      rewrite nth_error_map in Hnth.
      destruct (nth_error bs j) as [[cj0 bj0]|] eqn:Horig;
        cbn in Hnth; [|discriminate].
      inversion Hnth; subst cj bj.
      destruct (e2 j cj0 bj0 Hj Horig) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite (enum_pos_lift_id cj0 nj Hpos d k0). exact Hpos.
      * exact Hneq.
    + apply H.
    + apply H0.
Qed.
