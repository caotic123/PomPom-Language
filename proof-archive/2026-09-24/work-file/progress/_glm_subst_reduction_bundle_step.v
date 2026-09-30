(* GLM worker 1 — step_subst_glm: substituting the SAME term u at cutoff k   *)
(* commutes with small-step reduction.  Companion to _glm_step_lift_glm.     *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules Progress.

Theorem step_subst_glm : forall t v, step t v -> forall u k,
    step (subst u k t) (subst u k v).
Proof.
  intros t v H.
  induction H; intros u kk;
    try solve [cbn; constructor; eauto];
    try solve [cbn;
               repeat rewrite subst_lift_one_zero;
               repeat rewrite subst_lift_one_one;
               repeat rewrite subst_lift_one_zero;
               repeat rewrite subst_lift_two_zero;
               constructor];
    try solve [cbn; rewrite subst_subst_zero_comm; constructor].
  - (* st_case: raw case reduction — the side conditions transport through
       nth_error_subst_branches and enum_pos_subst_id; case bodies keep
       cutoff S k. *)
    cbn. rewrite subst_subst_zero_comm.
    eapply st_case with (k := k) (c := subst u kk c) (b := subst u (S kk) b)
                         (n := n).
    + eapply nth_error_subst_branches; exact H.
    + rewrite (enum_pos_subst_id c n H0 u kk). exact H0.
    + rewrite (enum_pos_subst_id a n H1 u kk). exact H1.
    + intros j cj bj Hj Hnthj.
      rewrite nth_error_map in Hnthj.
      destruct (nth_error bs j) as [[cj0 bj0]|] eqn:Horig;
        cbn in Hnthj; [|discriminate].
      inversion Hnthj; subst.
      destruct (H2 j cj0 bj0 Hj Horig) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite (enum_pos_subst_id cj0 nj Hpos u kk). exact Hpos.
      * exact Hneq.
  - (* st_case_lbl: clause labels evaluate in place — congruence under map. *)
    cbn. rewrite !map_app. cbn [map].
    constructor; eauto.
Qed.
