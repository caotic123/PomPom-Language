(* GLM worker 1 — cjoin-subst bundle, part 2: mutual epstep/epbranches
   substitution under the SAME arbitrary substituent. *)

Require Import Progress _tmp_epstep.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules.

Lemma epstep_var_subst_same_glm : forall n u k,
    epstep (subst u k (TVar n)) (subst u k (TVar n)).
Proof.
  intros n u k.
  destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
  - assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
    cbn [subst]. rewrite Hlt. apply epstep_refl.
  - subst n.
    assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
    cbn [subst]. rewrite Hlt, Heq. apply epstep_refl.
  - assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
    cbn [subst]. rewrite Hlt, Heq. apply epstep_refl.
Qed.

Lemma epstep_epbranches_subst_same_glm :
  (forall t t' (H : epstep t t'), forall u k,
      epstep (subst u k t) (subst u k t')) /\
  (forall bs bs' (H : epbranches bs bs'), forall u k,
      epbranches
        (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
        (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs')).
Proof.
  apply epstep_epbranches_ind; cbn; intros;
    try solve [constructor; eauto using epstep_refl, epstep_lift].
  - (* eps_var *)
    change (epstep (subst u k (TVar n)) (subst u k (TVar n))).
    apply epstep_var_subst_same_glm.
  - (* eps_eta *)
    rewrite subst_lift_one_zero.
    eapply eps_eta. eauto.
Qed.

Corollary epstep_subst_same_glm : forall t t', epstep t t' -> forall u k,
    epstep (subst u k t) (subst u k t').
Proof. intros t t' H. exact (proj1 epstep_epbranches_subst_same_glm t t' H). Qed.

Corollary epbranches_subst_same_glm : forall bs bs', epbranches bs bs' ->
    forall u k,
    epbranches
      (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
      (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs').
Proof. intros bs bs' H. exact (proj2 epstep_epbranches_subst_same_glm bs bs' H). Qed.

Print Assumptions epstep_subst_same_glm.
Print Assumptions epbranches_subst_same_glm.
