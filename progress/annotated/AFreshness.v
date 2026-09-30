(* Eta freshness sees all type annotations, not just executable erasure. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.ABinding.

Lemma occurs_lift : forall t c, occurs c (lift 1 c t) = false.
Proof.
  induction t; intro c; cbn [lift occurs];
    try solve [destruct (n <? c) eqn:H; cbn [occurs]; apply Nat.eqb_neq;
      apply Nat.ltb_lt in H || apply Nat.ltb_ge in H; lia].
  all: repeat match goal with
    IH : forall c, occurs c (lift 1 c ?t) = false
      |- context [occurs ?c (lift 1 ?c ?t)] => rewrite (IH c)
  end; reflexivity.
Qed.

Lemma subst_unused : forall t c u v, occurs c t = false ->
  subst u c t = subst v c t.
Proof.
  induction t; intros c u v H; cbn [occurs] in H;
    repeat rewrite Bool.orb_false_iff in H;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    cbn [subst]; try solve [rewrite H; destruct (n <? c); reflexivity];
    f_equal; auto.
Qed.

Lemma lift_lower : forall t c u, occurs c t = false ->
  lift 1 c (subst u c t) = t.
Proof.
  induction t; intros c u H; cbn [occurs] in H;
    repeat rewrite Bool.orb_false_iff in H;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    cbn [subst lift]; try solve [f_equal; auto].
  rewrite H; destruct (n <? c) eqn:HN; cbn [lift].
  - now rewrite HN.
  - apply Nat.ltb_ge in HN; apply Nat.eqb_neq in H.
    assert (HP : Nat.pred n <? c = false) by (apply Nat.ltb_ge; lia).
    rewrite HP; f_equal; lia.
Qed.

Theorem occurs_false_iff_lift : forall t c,
  occurs c t = false <-> exists u, t = lift 1 c u.
Proof.
  intros t c; split.
  - intro H; exists (subst TUnit c t); symmetry; now apply lift_lower.
  - intros [u ->]; apply occurs_lift.
Qed.

Print Assumptions occurs_false_iff_lift.
