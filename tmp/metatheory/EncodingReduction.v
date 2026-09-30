From Stdlib Require Import List Arith Bool Lia.
Require Export EncodingWork.
Require Import OpenSignaturesDerivedTyping.
Require ProofDB.DBReduction.
Import ListNotations.
Module DC := ProofDB.DBCore.

Lemma encode_product : forall A B env,
  encode env (product A B) = DB.product (encode env A) (encode env B).
Proof.
  intros; unfold product, DB.product; cbn [encode]. f_equal.
  apply encode_fresh, fresh_not_free. cbn; auto.
Qed.
Lemma encode_diagonal : forall G P env,
  encode env (diagonal_motive G P) = DB.diagonal_motive (encode env G) (encode env P).
Proof.
  intros; unfold diagonal_motive, DB.diagonal_motive; cbn [encode encode_var].
  rewrite Nat.eqb_refl. repeat rewrite encode_fresh by (apply fresh_not_free; cbn;auto).
  reflexivity.
Qed.
Local Ltac encoded_fresh :=
  first [apply fresh_not_free; cbn; tauto |
    match goal with |- ~ In (S (fresh ?ts)) (free_vars ?tm) =>
      apply (above_fresh_not_free ts tm (S (fresh ts))); [cbn;tauto|lia]
    end].
Local Ltac root_encode :=
  cbn [encode DC.root_step root_step option_map];
  unfold Bot, DB.Bot, carrier, DB.carrier;
  repeat rewrite encode_subst;
  repeat rewrite encode_product;
  repeat rewrite encode_diagonal;
  cbn [encode encode_var];
  repeat rewrite Nat.eqb_refl;
  repeat rewrite encode_fresh by encoded_fresh;
  cbn [DB.lift];
  repeat match goal with |- context [?n =? S ?n] =>
    replace (n =? S n) with false by (symmetry; apply Nat.eqb_neq; lia)
  end;
  repeat rewrite ProofDB.DBParallelBase.lift_fuse_zero by lia;
  repeat rewrite ProofDB.DBParallelBase.lift_one_one_zero;
  try reflexivity.

Lemma encode_root : forall t env,
  option_map (encode env) (root_step t) = DC.root_step (encode env t).
Proof.
  intros t env; destruct t; cbn [root_step encode DC.root_step]; try reflexivity.
  all: repeat match goal with
    | |- option_map _ (match ?x with _ => _ end) = _ => destruct x
  end; root_encode.
Qed.


Lemma encode_root_step : forall t u env, root_step t = Some u ->
  DC.root_step (encode env t) = Some (encode env u).
Proof. intros t u env H; rewrite <- encode_root, H; reflexivity. Qed.
Lemma encode_root_inverse : forall t env u,
  DC.root_step (encode env t) = Some u ->
  exists v, root_step t = Some v /\ encode env v = u.
Proof.
  intros t env u H. rewrite <- encode_root in H.
  destruct (root_step t) as [v|] eqn:E; [|discriminate].
  exists v. split; [reflexivity|now inversion H].
Qed.
Theorem encode_reduction : forall t u, reduction t u -> forall env,
  DC.reduction (encode env t) (encode env u).
Proof.
  intros t u H; induction H; intro env; cbn [encode];
    try solve [constructor; auto].
  - apply DC.red_root; now apply encode_root_step.
  - cbn [encode_var]. rewrite Nat.eqb_refl, encode_fresh by assumption.
    apply DC.red_eta.
Qed.
Theorem encode_conversion : forall t u, conv t u -> forall env,
  DC.conv (encode env t) (encode env u).
Proof.
  fix IH 3. intros t u H env; destruct H.
  - apply DC.cv_step. induction H; cbn [encode];
      try solve [constructor; auto]. apply DC.st_root; now apply encode_root_step.
  - apply DC.cv_refl.
  - now apply DC.cv_sym, IH.
  - eapply DC.cv_trans; apply IH; eassumption.
  - cbn [encode encode_var]. rewrite Nat.eqb_refl, encode_fresh by assumption.
    apply DC.cv_eta.
  - assert (encode env t = encode env u).
    { apply encode_alpha; [reflexivity|apply alpha_closed_context;assumption]. }
    rewrite H0. apply DC.cv_refl.
  - apply DC.cv_compatible.
    match goal with H : compatible _ _ _ |- _ => destruct H end;
      cbn [encode]; constructor; apply IH; assumption.
Qed.
