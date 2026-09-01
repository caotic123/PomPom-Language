Require Import Progress _tmp_lower.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma lower_gap_var : forall n q r,
    lower q (lift 1 (S (q + r)) (TVar n)) =
    option_map (lift 1 (q + r)) (lower q (TVar n)).
Proof.
  intros n q r.
  destruct (Nat.lt_trichotomy n q) as [Hlt|[Heq|Hgt]].
  - assert (Hnq : n <? q = true) by (apply Nat.ltb_lt; lia).
    assert (Hncut : n <? S (q + r) = true) by
      (apply Nat.ltb_lt; lia).
    cbv [lift lower].
    rewrite Hncut, Hnq.
    assert (Hngap : Nat.ltb n (q + r) = true) by
      (apply Nat.ltb_lt; lia).
    change (Some (TVar n) =
      Some (if Nat.ltb n (q + r) then TVar n else TVar (1+n))).
    rewrite Hngap.
    reflexivity.
  - subst n.
    assert (Hqcut : q <? S (q + r) = true) by
      (apply Nat.ltb_lt; lia).
    assert (Hqq : q <? q = false) by (apply Nat.ltb_ge; lia).
    assert (Hqeq : q =? q = true) by (apply Nat.eqb_eq; reflexivity).
    cbv [lift lower].
    rewrite Hqcut, Hqq, Hqeq.
    cbn [option_map].
    reflexivity.
  - destruct (Nat.lt_ge_cases n (S (q + r))) as [Hgap|Hout].
    + assert (Hncut : n <? S (q + r) = true) by
        (apply Nat.ltb_lt; exact Hgap).
      assert (Hnq : n <? q = false) by (apply Nat.ltb_ge; lia).
      assert (Hneq : n =? q = false) by (apply Nat.eqb_neq; lia).
      assert (Hpredgap : Nat.pred n <? q + r = true) by
        (apply Nat.ltb_lt; destruct n; cbn in *; lia).
      cbv [lift lower].
      rewrite Hncut, Hnq, Hneq.
      cbn [option_map lift].
      change (Some (TVar (Nat.pred n)) =
        Some (if Nat.ltb (Nat.pred n) (q + r)
              then TVar (Nat.pred n)
              else TVar (1 + Nat.pred n))).
      rewrite Hpredgap.
      reflexivity.
    + assert (Hncut : n <? S (q + r) = false) by
        (apply Nat.ltb_ge; exact Hout).
      assert (Hsnq : (1 + n) <? q = false) by (apply Nat.ltb_ge; lia).
      assert (Hsneq : (1 + n) =? q = false) by
        (apply Nat.eqb_neq; lia).
      assert (Hnq : n <? q = false) by (apply Nat.ltb_ge; lia).
      assert (Hneq : n =? q = false) by (apply Nat.eqb_neq; lia).
      assert (Hpredgap : Nat.pred n <? q + r = false) by
        (apply Nat.ltb_ge; destruct n; cbn in *; lia).
      cbv [lift lower].
      rewrite Hncut, Hsnq, Hsneq, Hnq, Hneq.
      cbn [option_map lift].
      change (Some (TVar n) =
        Some (if Nat.ltb (Nat.pred n) (q + r)
              then TVar (Nat.pred n)
              else TVar (1 + Nat.pred n))).
      rewrite Hpredgap.
      f_equal.
      destruct n as [|n']; cbn in *; [exfalso; lia | reflexivity].
Qed.
