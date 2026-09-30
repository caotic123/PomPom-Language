Require Import Progress _glm_step_lift.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Lemma fstep_lift_parent : forall t u, fstep t u -> forall d k,
  fstep (lift d k t) (lift d k u).
Proof.
  intros t u H. induction H; intros d k; cbn [lift];
    try solve [constructor; eauto using step_lift_glm].
  - rewrite lift_lift_one_zero. apply fs_eta.
  - repeat rewrite map_app. cbn. apply fs_case_br1. apply IHfstep.
  - repeat rewrite map_app. cbn. apply fs_case_br2. apply IHfstep.
Qed.

Lemma fconv_lift_parent : forall t u, fconv t u -> forall d k,
  fconv (lift d k t) (lift d k u).
Proof.
  intros t u H. induction H; intros d k.
  - apply fc_step, fstep_lift_parent, H.
  - apply fc_refl.
  - apply fc_sym, IHfconv.
  - eapply fc_trans; eauto.
Qed.
Print Assumptions fconv_lift_parent.
