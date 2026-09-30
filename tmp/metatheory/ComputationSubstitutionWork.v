From Stdlib Require Import Lia.
Require Export nameless.DBNormalization.

Lemma computation_root_subst : forall t u, root_step t = Some u ->
  forall a c, root_step (subst a c t) = Some (subst a c u).
Proof.
  intros t u H a c; destruct t; cbn [root_step] in H; try discriminate;
    repeat match goal with H : match ?x with _ => _ end = Some _ |- _ =>
      destruct x; try discriminate end;
    inversion H; subst; unfold product, Bot, carrier, diagonal_motive;
    repeat progress (cbn [subst root_step]; unfold product, Bot, carrier, diagonal_motive; subst_norm); reflexivity.
Qed.
Lemma computation_subst : forall t u, computation t u -> forall a c,
  computation (subst a c t) (subst a c u).
Proof.
  intros t u H; induction H; intros arg cutoff;
    try solve [apply cmp_root; now apply computation_root_subst].
  all: cbn [subst]; solve [constructor; auto].
Qed.

Lemma substitution_reflects_normalization : forall t a c,
  Acc (fun u v => computation v u) (subst a c t) ->
  Acc (fun u v => computation v u) t.
Proof.
  intros t a c H; remember (subst a c t) as s eqn:HE.
  revert t HE; induction H as [s H IH]; intros t HE; subst s.
  constructor; intros u HU; apply (IH (subst a c u));
    [now apply computation_subst|reflexivity].
Qed.
Print Assumptions substitution_reflects_normalization.
