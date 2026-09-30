Require Import Progress _tmp_epstep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma epstep_subst_mut :
  (forall t t' (H : epstep t t'), forall u u' k,
      epstep u u' -> epstep (subst u k t) (subst u' k t')) /\
  (forall bs bs' (H : epbranches bs bs'), forall u u' k,
      epstep u u' ->
      epbranches
        (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
        (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) bs')).
Proof.
  apply epstep_epbranches_ind; cbn; intros;
    try solve [constructor; eauto using epstep_refl, epstep_lift].
  - change (epstep (subst u k (TVar n)) (subst u' k (TVar n))).
    destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
    + assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
      cbn [subst]. rewrite Hlt. apply epstep_refl.
    + subst n.
      assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
      cbn [subst]. rewrite Hlt, Heq. eapply epstep_lift. exact H.
    + assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
      cbn [subst]. rewrite Hlt, Heq. apply epstep_refl.
  - rewrite subst_lift_one_zero.
    eapply eps_eta. eauto.
Qed.

Corollary epstep_subst : forall t t', epstep t t' -> forall u u' k,
    epstep u u' -> epstep (subst u k t) (subst u' k t').
Proof. intros t t' H. exact (proj1 epstep_subst_mut t t' H). Qed.

Corollary epbranches_subst : forall bs bs', epbranches bs bs' ->
    forall u u' k, epstep u u' ->
    epbranches
      (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
      (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) bs').
Proof. intros bs bs' H. exact (proj2 epstep_subst_mut bs bs' H). Qed.
