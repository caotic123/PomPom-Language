From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBComputationSubstitution.

Lemma reduction_lift : forall t u, reduction t u -> forall d c,
  reduction (lift d c t) (lift d c u).
Proof.
  intros t u H; induction H; intros d c; try solve [cbn [lift]; constructor; auto].
  - apply red_root. destruct t; cbn [root_step] in H; try discriminate;
      repeat match goal with H : match ?x with _ => _ end = Some _ |- _ =>
        destruct x; try discriminate end;
      inversion H; subst;
      repeat progress (cbn [lift root_step]; unfold product, Bot, carrier, diagonal_motive; lift_norm);
      reflexivity.
  - cbn [lift]. rewrite lift_lift_one_zero. apply red_eta.
Qed.
Lemma reduction_subst : forall t u, reduction t u -> forall a c,
  reduction (subst a c t) (subst a c u).
Proof.
  intros t u H; induction H; intros arg cutoff; try solve [cbn [subst]; constructor; auto].
  - apply red_root; now apply computation_root_subst.
  - cbn [subst]. rewrite subst_lift_one_zero. apply red_eta.
Qed.

Definition full_SN t := Acc (fun u v => reduction v u) t.
Lemma full_SN_map_reflection : forall C,
  (forall t u, reduction t u -> reduction (C t) (C u)) ->
  forall t, full_SN (C t) -> full_SN t.
Proof.
  intros C HC t H; remember (C t) as s eqn:HE; revert t HE.
  induction H as [s H IH]; intros t HE; subst s.
  constructor; intros u HU; apply (IH (C u)); [now apply HC|reflexivity].
Qed.
Lemma full_SN_lift_reflection : forall t d c, full_SN (lift d c t) -> full_SN t.
Proof. intros t d c H; apply (full_SN_map_reflection (lift d c)); [intros; now apply reduction_lift|exact H]. Qed.
Lemma full_SN_subst_reflection : forall t a c, full_SN (subst a c t) -> full_SN t.
Proof. intros t a c H; apply (full_SN_map_reflection (subst a c)); [intros; now apply reduction_subst|exact H]. Qed.
Lemma full_SN_eta_body : forall f,
  full_SN (TApp (lift 1 0 f) (TVar 0)) -> full_SN f.
Proof.
  intros f H. apply (full_SN_lift_reflection f 1 0).
  apply (full_SN_map_reflection (fun t => TApp t (TVar 0)));
    [intros; now apply red_TApp_f|exact H].
Qed.
Lemma full_SN_lambda : forall b, full_SN b -> full_SN (TLam b).
Proof.
  intros b H; induction H as [b H IH]. constructor; intros u HU.
  inversion HU; subst; [discriminate| |now apply IH].
  apply full_SN_eta_body; constructor; exact H.
Qed.

Print Assumptions reduction_subst.
Print Assumptions full_SN_lambda.
