Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma pdev_lift_switch_local_test : forall E P p e,
    (forall d k, pdev (lift d k E) = lift d k (pdev E)) ->
    (forall d k, pdev (lift d k P) = lift d k (pdev P)) ->
    (forall d k, pdev (lift d k p) = lift d k (pdev p)) ->
    (forall d k, pdev (lift d k e) = lift d k (pdev e)) ->
    forall d k,
      pdev (lift d k (TSwitch E P p e)) =
      lift d k (pdev (TSwitch E P p e)).
Proof.
  intros E P p e HE HP Hp He d k. destruct E.
  all: pose proof (HE d k) as HEk.
  all: pose proof (HP d k) as HPk.
  all: pose proof (Hp d k) as Hpk.
  all: pose proof (He d k) as Hek.
  all: cbn [lift pdev] in HEk, HPk, Hpk, Hek |- *.
  all: try solve [congruence].
  - destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
  - destruct p.
    all: cbn [lift pdev] in Hpk |- *.
    all: try solve [congruence].
    + destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
    + destruct e.
      all: cbn [lift pdev] in Hek |- *.
      all: try solve [congruence].
      * destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
      * repeat rewrite (lift_lift_one_zero _ _ _).
        repeat rewrite (lift_lift_one_one _ _ _).
        assert (HE2 : pdev (lift d k E2) = lift d k (pdev E2))
          by now injection HEk.
        assert (Hps : pdev (lift d k p2) = lift d k (pdev p2))
          by now injection Hpk.
        assert (Hn : pdev (lift d k e) = lift d k (pdev e))
          by now injection Hek.
        rewrite HE2, HPk, Hps, Hn.
        destruct k; cbn; reflexivity.
Qed.
