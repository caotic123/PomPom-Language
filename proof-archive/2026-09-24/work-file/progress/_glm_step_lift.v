(* GLM worker 1 — step_lift_glm: lifting commutes with small-step reduction. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules Progress.

Theorem step_lift_glm : forall t u, step t u -> forall d k,
    step (lift d k t) (lift d k u).
Proof.
  intros t u H.
  induction H; intros d kk;
    try solve [cbn; constructor; eauto];
    try solve [cbn;
               repeat rewrite (lift_lift_one_zero _ d kk);
               repeat rewrite (lift_lift_one_one _ d kk);
               repeat rewrite (lift_lift_one_zero _ d kk);
               repeat rewrite (lift_lift_two_zero _ d kk);
               constructor];
    try solve [cbn; rewrite lift_subst_zero_comm; constructor].
  - (* st_case: raw case reduction — the side conditions transport through
       nth_error_lift_branches and enum_pos_lift_id. *)
    cbn. rewrite lift_subst_zero_comm.
    eapply st_case with (k := k) (c := lift d kk c) (b := lift d (S kk) b)
                        (n := n).
    + eapply nth_error_lift_branches; exact H.
    + rewrite (enum_pos_lift_id c n H0 d kk). exact H0.
    + rewrite (enum_pos_lift_id a n H1 d kk). exact H1.
    + intros j cj bj Hj Hnthj.
      rewrite nth_error_map in Hnthj.
      destruct (nth_error bs j) as [[cj0 bj0]|] eqn:Horig;
        cbn in Hnthj; [|discriminate].
      inversion Hnthj; subst.
      destruct (H2 j cj0 bj0 Hj Horig) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite (enum_pos_lift_id cj0 nj Hpos d kk). exact Hpos.
      * exact Hneq.
  - (* st_case_lbl: clause labels evaluate in place — congruence under map. *)
    cbn. rewrite !map_app. cbn [map].
    constructor; eauto.
Qed.
