Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma subst_eta_beta_cancel_var : forall n k,
    subst (TVar 0) k (lift 1 (S k) (TVar n)) = TVar n.
Proof.
  intros n k. cbn [lift].
  destruct (Nat.ltb n (S k)) eqn:Hn.
  - apply Nat.ltb_lt in Hn. cbn [subst].
    destruct (Nat.eq_dec n k) as [->|Hneq].
    + rewrite Nat.ltb_irrefl, Nat.eqb_refl. cbn [lift].
      replace (k + 0) with k by lia. reflexivity.
    + assert (Hlt : Nat.ltb n k = true) by
        (apply Nat.ltb_lt; lia).
      rewrite Hlt. reflexivity.
  - apply Nat.ltb_ge in Hn. cbn [subst].
    assert (Hlt : Nat.ltb (1+n) k = false) by
      (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb (1+n) k = false) by
      (apply Nat.eqb_neq; lia).
    rewrite Hlt, Heq. f_equal.
Qed.

Lemma subst_eta_beta_cancel_gen : forall t k,
    subst (TVar 0) k (lift 1 (S k) t) = t.
Proof.
  apply (tsize_strong_ind (fun t => forall k,
    subst (TVar 0) k (lift 1 (S k) t) = t)).
  intros t IH k. destruct t; cbn [lift subst].
  all: try solve [apply subst_eta_beta_cancel_var].
  all: try reflexivity.
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    reflexivity].
  rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) k).
  rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) k).
  f_equal.
  induction bs as [|[c b] bs IHbs]; cbn; [reflexivity |].
  f_equal.
  f_equal.
  - apply IH. eapply tsize_case_bs. left. reflexivity.
  - apply IH. eapply tsize_case_bs_body. left. reflexivity.
  - apply IHbs. intros u Hu. apply IH. cbn in *. lia.
Qed.

Corollary subst_eta_beta_cancel : forall t,
    subst (TVar 0) 0 (lift 1 1 t) = t.
Proof. intros t. apply subst_eta_beta_cancel_gen. Qed.
