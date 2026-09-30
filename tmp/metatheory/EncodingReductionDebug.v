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
    eapply above_fresh_not_free; [cbn; tauto|lia]].
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
  repeat rewrite ProofDB.DBParallelBase.lift_one_one_zero;
  try reflexivity.

Lemma encode_root : forall t env,
  option_map (encode env) (root_step t) = DC.root_step (encode env t).
Proof.
  intros t env; destruct t; cbn [root_step encode DC.root_step]; try reflexivity.
  all: repeat match goal with
    | |- option_map _ (match ?x with _ => _ end) = _ => destruct x
  end; root_encode.
Show.
Abort.
