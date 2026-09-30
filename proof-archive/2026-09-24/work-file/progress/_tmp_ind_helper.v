Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma pdev_lift_ind_local : forall R P s i x,
    (forall d k, pdev (lift d k R) = lift d k (pdev R)) ->
    (forall d k, pdev (lift d k P) = lift d k (pdev P)) ->
    (forall d k, pdev (lift d k s) = lift d k (pdev s)) ->
    (forall d k, pdev (lift d k i) = lift d k (pdev i)) ->
    (forall d k, pdev (lift d k x) = lift d k (pdev x)) ->
    forall d k,
      pdev (lift d k (TInd R P s i x)) =
      lift d k (pdev (TInd R P s i x)).
Proof.
  intros R P s i x HR HP Hs Hi Hx d k. destruct x.
  all: pose proof (HR d k) as HRk.
  all: pose proof (HP d k) as HPk.
  all: pose proof (Hs d k) as Hsk.
  all: pose proof (Hi d k) as Hik.
  all: pose proof (Hx d k) as Hxk.
  all: cbn [lift pdev] in HRk, HPk, Hsk, Hik, Hxk |- *.
  all: try solve [
    repeat first [rewrite HRk | rewrite HPk | rewrite Hsk |
                  rewrite Hik | rewrite Hxk]; reflexivity].
  - destruct (Nat.ltb n k); cbn [lift pdev];
      rewrite HRk, HPk, Hsk, Hik; reflexivity.
  - assert (Hinner : pdev (lift d k x) = lift d k (pdev x)).
    { now injection Hxk. }
    rewrite HRk, HPk, Hsk, Hik, Hinner.
    repeat rewrite (lift_lift_two_zero _ _ _).
    reflexivity.
Qed.
