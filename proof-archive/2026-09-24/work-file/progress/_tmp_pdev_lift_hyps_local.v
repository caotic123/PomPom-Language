Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma pdev_lift_hyps_local : forall D X P h x,
    (forall d k, pdev (lift d k D) = lift d k (pdev D)) ->
    (forall d k, pdev (lift d k X) = lift d k (pdev X)) ->
    (forall d k, pdev (lift d k P) = lift d k (pdev P)) ->
    (forall d k, pdev (lift d k h) = lift d k (pdev h)) ->
    (forall d k, pdev (lift d k x) = lift d k (pdev x)) ->
    forall d k,
      pdev (lift d k (THyps D X P h x)) =
      lift d k (pdev (THyps D X P h x)).
Proof.
  intros D X P h x HD HX HP Hh Hx d k.
  destruct D.
  all: pose proof (HD d k) as HDk;
    pose proof (HX d k) as HXk;
    pose proof (HP d k) as HPk;
    pose proof (Hh d k) as Hhk;
    pose proof (Hx d k) as Hxk;
    cbn [lift pdev] in HDk, HXk, HPk, Hhk, Hxk |- *.
  all: try solve [
    repeat first [rewrite HDk | rewrite HXk | rewrite HPk |
                  rewrite Hhk | rewrite Hxk]; reflexivity].
  - destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
  - injection HDk as HD1.
    rewrite Hhk, Hxk, HD1; reflexivity.
  - destruct x; cbn [lift pdev] in Hxk |- *; try congruence.
    destruct (Nat.ltb n k); cbn [lift pdev];
      rewrite HXk, HPk, Hhk; congruence.
  - destruct x; cbn [lift pdev] in Hxk |- *; try solve [congruence].
    injection HDk as HD1 HD2.
    destruct (Nat.ltb n k); cbn [lift pdev];
      rewrite HXk, HPk, Hhk, HD1, HD2; congruence.
  - injection HDk as HD1 HD2.
    rewrite HD2, HXk, HPk, Hhk, Hxk.
    repeat rewrite (lift_lift_one_zero _ _ _).
    cbn [lift]. reflexivity.
  - destruct x.
    all: cbn [lift pdev] in Hxk |- *.
    all: try solve [congruence].
    injection HDk as HD1 HD2.
    destruct (Nat.ltb n k); cbn [lift pdev];
      rewrite HXk, HPk, Hhk, HD1, HD2; congruence.
Qed.
