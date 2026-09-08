From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules Progress.

Lemma dbg_interp_pi :
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
    match goal with |- ?G => idtac "BULLET11 GOAL:" G end.
    eapply ps_interp_pi.
    + eauto.
    + (* inspect the T goal *)
      match goal with |- ?G => idtac "TGOAL:" G end.
      admit.
    + eauto.
Abort.
