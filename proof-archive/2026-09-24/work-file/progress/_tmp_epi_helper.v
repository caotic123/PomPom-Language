Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma pdev_lift_epi_local_test : forall E P,
    (forall d k, pdev (lift d k E) = lift d k (pdev E)) ->
    (forall d k, pdev (lift d k P) = lift d k (pdev P)) ->
    forall d k, pdev (lift d k (TEPi E P)) = lift d k (pdev (TEPi E P)).
Proof.
  intros E P HE HP d k. destruct E.
  all: pose proof (HE d k) as HEk.
  all: pose proof (HP d k) as HPk.
  all: cbn [lift pdev] in HEk, HPk |- *.
  all: try solve [rewrite HPk; f_equal; exact HEk].
  - destruct (Nat.ltb n k); cbn [lift pdev]; rewrite HPk; reflexivity.
  - reflexivity.
  - assert (Ht : pdev (lift d k E2) = lift d k (pdev E2)).
    { now injection HEk. }
    rewrite HPk, Ht.
    repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _).
    reflexivity.
Qed.
