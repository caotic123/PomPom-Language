Require Import Progress.
Require Import _tmp_case_lift.
Require Import _tmp_hyps_full.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Ltac add_term_sizes :=
  repeat match goal with
  | x : term |- _ =>
      match goal with
      | _ : 1 <= tsize x |- _ => fail 1
      | _ => let H := fresh "Hsz" in pose proof (tsize_pos x) as H
      end
  end.

Ltac finish_pdev_lift IH :=
  repeat match goal with
  | H : pdev (lift _ _ _) = _ |- _ => rewrite H; clear H
  end;
  repeat match goal with
  | |- context [Nat.ltb ?n ?k] =>
      destruct (Nat.ltb n k) eqn:?; cbn [lift pdev]
  end;
  repeat erewrite IH by
    (add_term_sizes; cbn; lia);
  repeat rewrite lift_subst_zero_comm;
  repeat rewrite (lift_lift_one_zero _ _ _);
  repeat rewrite (lift_lift_one_one _ _ _);
  repeat rewrite (lift_lift_two_zero _ _ _);
  reflexivity.

Ltac pose_pdev_ih IH u d k :=
  let H := fresh "Hdev" in
  assert (H : pdev (lift d k u) = lift d k (pdev u))
    by (apply IH; add_term_sizes; cbn; lia).

Lemma pdev_lift_app_local : forall f a,
    (forall d k, pdev (lift d k f) = lift d k (pdev f)) ->
    (forall d k, pdev (lift d k a) = lift d k (pdev a)) ->
    forall d k,
      pdev (lift d k (TApp f a)) = lift d k (pdev (TApp f a)).
Proof.
  intros f a Hf Ha d k.
  destruct f.
  all: try solve [
    pose proof (Hf d k) as Hfk;
    pose proof (Ha d k) as Hak;
    cbn [lift pdev] in Hfk, Hak |- *;
    rewrite Hak; f_equal; exact Hfk].
  - cbn [lift pdev].
    destruct (Nat.ltb n k); cbn [lift pdev]; rewrite Ha; reflexivity.
  - pose proof (Hf d k) as Hfk.
    pose proof (Ha d k) as Hak.
    cbn [lift pdev] in Hfk, Hak |- *.
    inversion Hfk as [Hb].
    rewrite Hak, Hb, lift_subst_zero_comm. reflexivity.
Qed.

Lemma pdev_lift_fst_local : forall p,
    (forall d k, pdev (lift d k p) = lift d k (pdev p)) ->
    forall d k, pdev (lift d k (TFst p)) = lift d k (pdev (TFst p)).
Proof.
  intros p Hp d k. destruct p.
  all: pose proof (Hp d k) as Hpk.
  all: cbn [lift pdev] in Hpk |- *.
  all: try solve [f_equal; exact Hpk].
  - destruct (Nat.ltb n k); reflexivity.
  - now injection Hpk.
Qed.

Lemma pdev_lift_snd_local : forall p,
    (forall d k, pdev (lift d k p) = lift d k (pdev p)) ->
    forall d k, pdev (lift d k (TSnd p)) = lift d k (pdev (TSnd p)).
Proof.
  intros p Hp d k. destruct p.
  all: pose proof (Hp d k) as Hpk.
  all: cbn [lift pdev] in Hpk |- *.
  all: try solve [f_equal; exact Hpk].
  - destruct (Nat.ltb n k); reflexivity.
  - now injection Hpk.
Qed.

Lemma pdev_lift_epi_local : forall E P,
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

Lemma pdev_lift_switch_local : forall E P p e,
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

Lemma pdev_lift_interp_local : forall D X,
    (forall d k, pdev (lift d k D) = lift d k (pdev D)) ->
    (forall d k, pdev (lift d k X) = lift d k (pdev X)) ->
    forall d k,
      pdev (lift d k (TInterp D X)) =
      lift d k (pdev (TInterp D X)).
Proof.
  intros D X HD HX d k. destruct D.
  all: pose proof (HD d k) as HDk;
    pose proof (HX d k) as HXk;
    cbn [lift pdev] in HDk, HXk |- *.
  all: try solve [rewrite HXk; f_equal; exact HDk].
  - destruct (Nat.ltb n k); cbn [lift pdev]; rewrite HXk; reflexivity.
  - injection HDk as HD1. rewrite HXk; f_equal; exact HD1.
  - reflexivity.
  - injection HDk as HD1 HD2. rewrite HXk, HD1, HD2.
    repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _). reflexivity.
  - injection HDk as HD1 HD2. rewrite HXk, HD1, HD2.
    repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _). cbn [lift]. reflexivity.
  - injection HDk as HD1 HD2. rewrite HXk, HD1, HD2.
    repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _). reflexivity.
  - injection HDk as HD1 HD2. rewrite HXk, HD1, HD2.
    repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _). reflexivity.
Qed.

Lemma pdev_lift_iall_local : forall D X x P,
    (forall d k, pdev (lift d k D) = lift d k (pdev D)) ->
    (forall d k, pdev (lift d k X) = lift d k (pdev X)) ->
    (forall d k, pdev (lift d k x) = lift d k (pdev x)) ->
    (forall d k, pdev (lift d k P) = lift d k (pdev P)) ->
    forall d k,
      pdev (lift d k (TIAll D X x P)) =
      lift d k (pdev (TIAll D X x P)).
Proof.
  intros D X x P HD HX Hx HP d k. destruct D.
  all: pose proof (HD d k) as HDk.
  all: pose proof (HX d k) as HXk.
  all: pose proof (Hx d k) as Hxk.
  all: pose proof (HP d k) as HPk.
  all: cbn [lift pdev] in HDk, HXk, Hxk, HPk |- *.
  all: try solve [congruence].
  - destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
  - destruct x; cbn [lift pdev] in Hxk |- *; try solve [congruence].
    destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
  - destruct x; cbn [lift pdev] in Hxk |- *; try solve [congruence].
    + destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
    + repeat rewrite (lift_lift_one_zero _ _ _).
      repeat rewrite (lift_lift_one_one _ _ _). congruence.
  - repeat rewrite (lift_lift_one_zero _ _ _).
    repeat rewrite (lift_lift_one_one _ _ _).
    destruct k; cbn; congruence.
  - destruct x; cbn [lift pdev] in Hxk |- *; try solve [congruence].
    destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
  - destruct x; cbn [lift pdev] in Hxk |- *; try solve [congruence].
    destruct (Nat.ltb n k); cbn [lift pdev]; congruence.
Qed.

Lemma try_pdev_lift : forall t d k,
    pdev (lift d k t) = lift d k (pdev t).
Proof.
  apply (tsize_strong_ind
    (fun t => forall d k,
      pdev (lift d k t) = lift d k (pdev t))).
  intros t IH d k. destruct t; cbn [lift pdev].
  all: try solve [
    destruct k as [|k]; cbn; [reflexivity |];
    destruct (Nat.leb n k); reflexivity].
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5));
       cbn; lia);
    reflexivity].
  - apply pdev_lift_app_local.
    + intros d' k'. apply IH; add_term_sizes; cbn; lia.
    + intros d' k'. apply IH; add_term_sizes; cbn; lia.
  - apply pdev_lift_fst_local. intros d' k'.
    apply IH; add_term_sizes; cbn; lia.
  - apply pdev_lift_snd_local. intros d' k'.
    apply IH; add_term_sizes; cbn; lia.
  - apply pdev_lift_epi_local.
    + intros d' k'. apply IH; add_term_sizes; cbn; lia.
    + intros d' k'. apply IH; add_term_sizes; cbn; lia.
  - apply pdev_lift_switch_local.
    all: intros d' k'; apply IH; add_term_sizes; cbn; lia.
  - apply pdev_lift_interp_local.
    all: intros d' k'; apply IH; add_term_sizes; cbn; lia.
  - apply pdev_lift_ind_local.
    all: intros d' k'; apply IH; add_term_sizes; cbn; lia.
  - apply pdev_lift_iall_local.
    all: intros d' k'; apply IH; add_term_sizes; cbn; lia.
  - apply pdev_lift_hyps_local_test.
    all: intros d' k'; apply IH; add_term_sizes; cbn; lia.
  - apply pdev_lift_case_local.
    + intros d' k'. apply IH; pose proof (tsize_pos t2); cbn; lia.
    + intros d' k'. apply IH; pose proof (tsize_pos t1); cbn; lia.
    + intros c b Hin d' k'. split.
      * apply IH. eapply tsize_case_bs; exact Hin.
      * apply IH. eapply tsize_case_bs_body; exact Hin.
Qed.
