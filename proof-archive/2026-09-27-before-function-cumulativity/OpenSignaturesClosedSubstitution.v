From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesSubstitution.
Import ListNotations.

Lemma typed_closed : forall t A, typing empty_ctx t A -> free_vars t = [].
Proof.
  intros t A H. destruct (free_vars t) as [|x xs] eqn:E; [reflexivity|].
  exfalso. apply (typing_fresh_not_free _ _ _ x H eq_refl). rewrite E; now left.
Qed.

Lemma closed_substitution_binder : forall u k x b,
  free_vars u = [] -> substitution_binder (fun y => if Nat.eqb y k then u else TVar y) x b = x.
Proof.
  intros u k x b Hu. unfold substitution_binder.
  assert (Hnone : existsb (Nat.eqb x)
    (flat_map (fun y => free_vars (if Nat.eqb y k then u else TVar y))
      (remove Nat.eq_dec x (free_vars b))) = false).
  { apply Bool.not_true_is_false. intros Htrue.
    apply existsb_exists in Htrue; destruct Htrue as [z [Hz Heq]].
    apply Nat.eqb_eq in Heq; subst z. apply in_flat_map in Hz; destruct Hz as [y [Hy Hxy]].
    destruct (Nat.eqb y k); [rewrite Hu in Hxy; contradiction|].
    cbn [free_vars] in Hxy; destruct Hxy as [->|[]].
    rewrite in_remove_iff in Hy; tauto. }
  now rewrite Hnone.
Qed.

Lemma bind_closed_substitution : forall u k x b,
  k <> x ->
  substitute (bind_substitution (fun y => if Nat.eqb y k then u else TVar y) x x) b = subst u k b.
Proof.
  intros u k x b Hne. apply substitute_ext_on; intros y Hy.
  unfold bind_substitution. destruct (Nat.eqb y x) eqn:E; [|reflexivity].
  apply Nat.eqb_eq in E; subst y. assert (Exk : Nat.eqb x k = false) by (apply Nat.eqb_neq; congruence).
  now rewrite Exk.
Qed.

Lemma subst_closed_lam : forall u k x t,
  free_vars u = [] -> k <> x -> subst u k (TLam x t) = TLam x (subst u k t).
Proof.
  intros u k x t Hu Hne. unfold subst at 1; cbn [substitute].
  rewrite closed_substitution_binder by assumption.
  now rewrite bind_closed_substitution.
Qed.
Lemma subst_closed_pi : forall u k x A B,
  free_vars u = [] -> k <> x ->
  subst u k (TPi x A B) = TPi x (subst u k A) (subst u k B).
Proof.
  intros u k x A B Hu Hne. unfold subst at 1; cbn [substitute].
  rewrite closed_substitution_binder by assumption.
  now rewrite bind_closed_substitution.
Qed.

Lemma subst_closed_commute : forall t u v x y,
  free_vars u = [] -> free_vars v = [] -> x <> y ->
  alpha_equiv (subst v y (subst u x t)) (subst u x (subst v y t)).
Proof.
  intros t u v x y Hu Hv Hne. unfold subst.
  etransitivity; [apply substitute_compose|].
  etransitivity; [|symmetry;apply substitute_compose].
  apply substitute_alpha; [reflexivity|]. intros z Hz.
  destruct (Nat.eqb z x) eqn:Ex; destruct (Nat.eqb z y) eqn:Ey.
  - apply Nat.eqb_eq in Ex, Ey; congruence.
  - fold (subst v y u). rewrite subst_fresh by (rewrite Hu; tauto).
    cbn [substitute]. rewrite Ex. reflexivity.
  - fold (subst u x v). rewrite subst_fresh by (rewrite Hv; tauto).
    cbn [substitute]. rewrite Ey. reflexivity.
  - cbn [substitute]. rewrite Ex,Ey. reflexivity.
Qed.
