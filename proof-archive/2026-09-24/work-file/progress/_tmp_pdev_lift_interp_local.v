Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma pdev_lift_interp_local : forall D X,
    (forall d k, pdev (lift d k D) = lift d k (pdev D)) ->
    (forall d k, pdev (lift d k X) = lift d k (pdev X)) ->
    forall d k,
      pdev (lift d k (TInterp D X)) =
      lift d k (pdev (TInterp D X)).
Proof.
  intros D X HD HX d k.
  destruct D.
  all: pose proof (HD d k) as HDk;
    pose proof (HX d k) as HXk;
    cbn [lift pdev] in HDk, HXk |- *.
  all: try solve [rewrite HXk; f_equal; exact HDk].
  - destruct (Nat.ltb n k); cbn [lift pdev]; rewrite HXk; reflexivity.
  - injection HDk as HD1.
    rewrite HXk; f_equal; exact HD1.
  - reflexivity.
  - injection HDk as HD1 HD2.
    rewrite HXk, HD1, HD2.
    repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _).
    reflexivity.
  - injection HDk as HD1 HD2.
    rewrite HXk, HD1, HD2.
    repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _).
    cbn [lift]. reflexivity.
  - injection HDk as HD1 HD2.
    rewrite HXk, HD1, HD2.
    repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _).
    reflexivity.
  - injection HDk as HD1 HD2.
    rewrite HXk, HD1, HD2.
    repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _).
    reflexivity.
Qed.
