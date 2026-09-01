Require Import Progress _tmp_lower.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma lower_lift_succ_var : forall n k,
    lower k (lift 1 (S k) (TVar n)) =
    option_map (lift 1 k) (lower k (TVar n)).
Proof.
  intros n k.
  destruct (Nat.lt_trichotomy n k) as [Hlt|[Heq|Hgt]].
  - assert (Hnk : n <? k = true) by (apply Nat.ltb_lt; lia).
    assert (Hnsk : n <? S k = true) by (apply Nat.ltb_lt; lia).
    cbv [lift lower]. rewrite Hnsk. repeat rewrite Hnk.
    cbn [option_map lift]. rewrite Hnk. reflexivity.
  - subst n.
    assert (Hksk : k <? S k = true) by (apply Nat.ltb_lt; lia).
    assert (Hkk : k <? k = false) by (apply Nat.ltb_ge; lia).
    assert (Hkeq : k =? k = true) by (apply Nat.eqb_eq; reflexivity).
    cbv [lift lower]. rewrite Hksk. rewrite Hkk, Hkeq.
    cbn [option_map]. reflexivity.
  - assert (Hnsk : n <? S k = false) by (apply Nat.ltb_ge; lia).
    assert (Hsnk : 1+n <? k = false) by (apply Nat.ltb_ge; lia).
    assert (Hsneq : 1+n =? k = false) by (apply Nat.eqb_neq; lia).
    assert (Hnk : n <? k = false) by (apply Nat.ltb_ge; lia).
    assert (Hneq : n =? k = false) by (apply Nat.eqb_neq; lia).
    assert (Hpred : Nat.pred n <? k = false) by
      (apply Nat.ltb_ge; destruct n; cbn in *; lia).
    cbv [lift lower].
    rewrite Hnsk, Hsnk, Hsneq, Hnk, Hneq.
    cbn [option_map lift]. rewrite Hpred.
    f_equal. destruct n; [lia | reflexivity].
Qed.

Lemma lower_lift_succ_bs_bound : forall N,
    (forall u, tsize u < N -> forall k,
      lower k (lift 1 (S k) u) =
      option_map (lift 1 k) (lower k u)) ->
    forall k bs, bsize bs < N ->
      lower_bs lower k
        (map (fun '(c,b) => (lift 1 (S k) c, lift 1 (S (S k)) b)) bs) =
      option_map
        (map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)))
        (lower_bs lower k bs).
Proof.
  intros N H k bs. revert k.
  induction bs as [|[c b] bs IH]; intros k Hsize; cbn; [reflexivity |].
  assert (Hc : tsize c < N) by
    (pose proof (tsize_pos b); cbn in Hsize; lia).
  assert (Hb : tsize b < N) by
    (pose proof (tsize_pos c); cbn in Hsize; lia).
  rewrite (H c Hc k), (H b Hb (S k)), (IH k ltac:(cbn in Hsize; lia)).
  destruct (lower k c); destruct (lower (S k) b);
    destruct (lower_bs lower k bs); reflexivity.
Qed.

Lemma lower_lift_succ : forall t k,
    lower k (lift 1 (S k) t) =
    option_map (lift 1 k) (lower k t).
Proof.
  apply (tsize_strong_ind (fun t => forall k,
    lower k (lift 1 (S k) t) = option_map (lift 1 k) (lower k t))).
  intros t IH k. destruct t; cbn [lift lower].
  all: try solve [apply lower_lift_succ_var].
  all: try reflexivity.
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    repeat match goal with
    | |- context [lower ?q ?u] => destruct (lower q u)
    end;
    reflexivity].
  rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) k).
  rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) k).
  rewrite (lower_lift_succ_bs_bound (tsize (TCase t1 t2 bs))
    (fun u Hu q => IH u Hu q) k bs ltac:(cbn; lia)).
  destruct (lower k t1); destruct (lower k t2);
    destruct (lower_bs lower k bs); reflexivity.
Qed.

Lemma lift_eta_shape_decomp : forall f h,
    lift 1 0 f = TLam (TApp (lift 1 0 h) (TVar 0)) ->
    exists u, h = lift 1 0 u.
Proof.
  intros f h Heq. destruct f; cbn [lift] in Heq; try discriminate.
  inversion Heq; subst.
  destruct f; cbn [lift] in H0; try discriminate.
  - destruct (Nat.ltb n 1); discriminate.
  - inversion H0; subst.
    match goal with
    | Hfg : lift 1 1 ?g = lift 1 0 h |- _ =>
        pose proof (f_equal (lower 0) Hfg) as Hlow
    end.
    rewrite lower_lift, lower_lift_succ in Hlow.
    destruct (lower 0 f1) as [u|] eqn:Hf; cbn in Hlow; try discriminate.
    inversion Hlow; subst. exists u. reflexivity.
Qed.

Lemma lower_lift_gap_var : forall n q r,
    lower q (lift 1 (S (q + r)) (TVar n)) =
    option_map (lift 1 (q + r)) (lower q (TVar n)).
Proof.
  intros n q r.
  destruct (Nat.lt_trichotomy n q) as [Hlt|[Heq|Hgt]].
  - assert (Hsrc : n <? S (q + r) = true) by
      (apply Nat.ltb_lt; lia).
    assert (Hq : n <? q = true) by (apply Nat.ltb_lt; lia).
    assert (Hout : n <? q + r = true) by (apply Nat.ltb_lt; lia).
    cbv [lift lower]. rewrite Hsrc, Hq.
    cbn [option_map lift]. rewrite Hout. reflexivity.
  - subst n.
    assert (Hsrc : q <? S (q + r) = true) by
      (apply Nat.ltb_lt; lia).
    assert (Hlt : q <? q = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : q =? q = true) by (apply Nat.eqb_eq; reflexivity).
    cbv [lift lower]. rewrite Hsrc, Hlt, Heq. reflexivity.
  - assert (Hq : n <? q = false) by (apply Nat.ltb_ge; lia).
    assert (Hneq : n =? q = false) by (apply Nat.eqb_neq; lia).
    destruct (n <? S (q + r)) eqn:Hsrc.
    + assert (Hout : Nat.pred n <? q + r = true).
      { apply Nat.ltb_lt. apply Nat.ltb_lt in Hsrc.
        destruct n; cbn in *; lia. }
      cbv [lift lower]. rewrite Hsrc, Hq, Hneq.
      cbn [option_map lift]. rewrite Hout. reflexivity.
    + assert (Hsrcq : 1 + n <? q = false) by
        (apply Nat.ltb_ge; lia).
      assert (Hsrceq : 1 + n =? q = false) by
        (apply Nat.eqb_neq; lia).
      assert (Hout : Nat.pred n <? q + r = false).
      { apply Nat.ltb_ge. apply Nat.ltb_ge in Hsrc.
        destruct n; cbn in *; lia. }
      cbv [lift lower]. rewrite Hsrc, Hsrcq, Hsrceq, Hq, Hneq.
      cbn [option_map lift]. rewrite Hout.
      destruct n; [lia | reflexivity].
Qed.

Lemma lower_lift_gap_bs_bound : forall N,
    (forall u, tsize u < N -> forall q r,
      lower q (lift 1 (S (q + r)) u) =
      option_map (lift 1 (q + r)) (lower q u)) ->
    forall q r bs, bsize bs < N ->
      lower_bs lower q
        (map (fun '(c,b) =>
          (lift 1 (S (q + r)) c,
           lift 1 (S (S (q + r))) b)) bs) =
      option_map
        (map (fun '(c,b) =>
          (lift 1 (q + r) c, lift 1 (S (q + r)) b)))
        (lower_bs lower q bs).
Proof.
  intros N H q r bs. revert q r.
  induction bs as [|[c b] bs IH]; intros q r Hsize; cbn; [reflexivity |].
  assert (Hc : tsize c < N) by
    (pose proof (tsize_pos b); cbn in Hsize; lia).
  assert (Hb : tsize b < N) by
    (pose proof (tsize_pos c); cbn in Hsize; lia).
  rewrite (H c Hc q r).
  pose proof (H b Hb (S q) r) as Hbody.
  replace (S q + r) with (S (q + r)) in Hbody by lia.
  rewrite Hbody, (IH q r ltac:(cbn in Hsize; lia)).
  destruct (lower q c); destruct (lower (S q) b);
    destruct (lower_bs lower q bs); reflexivity.
Qed.

Lemma lower_lift_gap : forall t q r,
    lower q (lift 1 (S (q + r)) t) =
    option_map (lift 1 (q + r)) (lower q t).
Proof.
  apply (tsize_strong_ind (fun t => forall q r,
    lower q (lift 1 (S (q + r)) t) =
    option_map (lift 1 (q + r)) (lower q t))).
  intros t IH q r. destruct t; cbn [lift lower].
  all: try solve [apply lower_lift_gap_var].
  all: try reflexivity.
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    repeat match goal with
    | |- context [lower ?qq ?u] => destruct (lower qq u)
    end;
    reflexivity].
  - rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) q r).
    pose proof (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia)
      (S q) r) as Hbody.
    replace (S q + r) with (S (q + r)) in Hbody by lia.
    rewrite Hbody.
    destruct (lower q t1); destruct (lower (S q) t2); reflexivity.
  - pose proof (IH t ltac:(cbn; lia) (S q) r) as Hbody.
    replace (S q + r) with (S (q + r)) in Hbody by lia.
    rewrite Hbody. destruct (lower (S q) t); reflexivity.
  - rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) q r).
    pose proof (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia)
      (S q) r) as Hbody.
    replace (S q + r) with (S (q + r)) in Hbody by lia.
    rewrite Hbody.
    destruct (lower q t1); destruct (lower (S q) t2); reflexivity.
  - rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) q r).
    rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) q r).
    rewrite (lower_lift_gap_bs_bound (tsize (TCase t1 t2 bs))
      (fun u Hu qq rr => IH u Hu qq rr) q r bs ltac:(cbn; lia)).
    destruct (lower q t1); destruct (lower q t2);
      destruct (lower_bs lower q bs); reflexivity.
Qed.

Lemma lift_one_injective : forall k x y,
    lift 1 k x = lift 1 k y -> x = y.
Proof.
  intros k x y Heq.
  pose proof (f_equal (lower k) Heq) as Hlow.
  repeat rewrite lower_lift in Hlow. now inversion Hlow.
Qed.

Lemma lift_eta_shape_decomp_k : forall f h k,
    lift 1 k f = TLam (TApp (lift 1 0 h) (TVar 0)) ->
    exists u,
      h = lift 1 k u /\
      f = TLam (TApp (lift 1 0 u) (TVar 0)).
Proof.
  intros f h k Heq.
  destruct f; cbn [lift] in Heq; try discriminate.
  - destruct (Nat.ltb n k); discriminate.
  - inversion Heq; subst.
    destruct f; cbn [lift] in H0; try discriminate.
    + destruct (Nat.ltb n (S k)); discriminate.
    + inversion H0; subst.
      assert (Harg' : lift 1 (S k) f2 = lift 1 (S k) (TVar 0))
        by (rewrite H2; reflexivity).
      apply lift_one_injective in Harg'. subst f2.
      pose proof (f_equal (lower 0) H1) as Hlow.
      rewrite lower_lift in Hlow.
      replace (S k) with (S (0 + k)) in Hlow by lia.
      rewrite lower_lift_gap in Hlow.
      destruct (lower 0 f1) as [u|] eqn:Hlower; cbn in Hlow;
        try discriminate.
      inversion Hlow; subst h.
      exists u. split; [reflexivity |].
      rewrite H2. f_equal. f_equal.
      apply lift_one_injective with (k := S k).
      rewrite lift_lift_one_zero. assumption.
Qed.
