Require Import Progress _tmp_epstep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma epstep_subst_var : forall n u u' k,
  epstep u u' ->
  epstep (subst u k (TVar n)) (subst u' k (TVar n)).
Proof.
  intros n u u' k H.
  destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
  - assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
    cbn [subst]. rewrite Hlt. constructor.
  - subst n.
    assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
    cbn [subst]. rewrite Hlt, Heq. eapply epstep_lift. exact H.
  - assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
    cbn [subst]. rewrite Hlt, Heq. constructor.
Qed.
