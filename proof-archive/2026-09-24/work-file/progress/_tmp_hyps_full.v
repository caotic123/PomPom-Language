Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma pdev_lift_hyps_local_test : forall D X P h x,
    (forall d k, pdev (lift d k D) = lift d k (pdev D)) ->
    (forall d k, pdev (lift d k X) = lift d k (pdev X)) ->
    (forall d k, pdev (lift d k P) = lift d k (pdev P)) ->
    (forall d k, pdev (lift d k h) = lift d k (pdev h)) ->
    (forall d k, pdev (lift d k x) = lift d k (pdev x)) ->
    forall d k,
      pdev (lift d k (THyps D X P h x)) =
      lift d k (pdev (THyps D X P h x)).
Proof.
  intros D X P h x HD HX HP Hh Hx d k. destruct D.
  all: pose proof (HD d k) as HDk.
  all: pose proof (HX d k) as HXk.
  all: pose proof (HP d k) as HPk.
  all: pose proof (Hh d k) as Hhk.
  all: pose proof (Hx d k) as Hxk.
  all: cbn [lift pdev] in HDk, HXk, HPk, Hhk, Hxk |- *.
  all: try solve [congruence].
  - destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
  - destruct x; cbn [lift pdev] in Hxk |- *; try solve [congruence].
    destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
  - destruct x; cbn [lift pdev] in Hxk |- *; try solve [congruence].
    destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
  - repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _).
    destruct k; cbn; congruence.
  - destruct x; cbn [lift pdev] in Hxk |- *; try solve [congruence].
    destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
  - destruct x; cbn [lift pdev] in Hxk |- *; try solve [congruence].
    destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
Qed.
