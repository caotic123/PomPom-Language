From Stdlib Require Import List Arith Bool Lia.
Require Import SubstitutionBase.
Import ListNotations.

Lemma substitution_free_binder : forall b,
  (forall sigma a, In a (free_vars (substitute sigma b)) <->
    exists v, In v (free_vars b) /\ In a (free_vars (sigma v))) ->
  forall sigma x a,
  In a (remove Nat.eq_dec (substitution_binder sigma x b)
    (free_vars (substitute (bind_substitution sigma x (substitution_binder sigma x b)) b))) <->
  exists v, In v (remove Nat.eq_dec x (free_vars b)) /\ In a (free_vars (sigma v)).
Proof.
  intros b IH sigma x a. rewrite in_remove_iff, IH. split.
  - intros [[v [Hv Ha]] Hneq]. unfold bind_substitution in Ha.
    destruct (v =? x) eqn:E.
    + cbn in Ha. destruct Ha as [<-|[]]. contradiction.
    + apply Nat.eqb_neq in E. exists v. split; [apply in_in_remove; assumption|exact Ha].
  - intros [v [Hv Ha]]. apply in_remove in Hv. destruct Hv as [Hv Hneq]. split.
    + exists v. split; [exact Hv|]. unfold bind_substitution.
      destruct (v =? x) eqn:E; [apply Nat.eqb_eq in E; contradiction|exact Ha].
    + intro E. subst a. exact (substitution_binder_fresh sigma x b v Hv Hneq Ha).
Qed.

Lemma free_vars_substitute : forall t sigma a,
  In a (free_vars (substitute sigma t)) <->
  exists v, In v (free_vars t) /\ In a (free_vars (sigma v)).
Proof.
  induction t; intros sigma v; cbn [substitute free_vars].
  all: repeat setoid_rewrite in_app_iff.
  all: try rewrite (substitution_free_binder _ IHt).
  all: try rewrite (substitution_free_binder _ IHt2).
  all: repeat setoid_rewrite in_app_iff.
  all: repeat match goal with
    | IH : forall sigma a, In a (free_vars (substitute sigma ?tm)) <-> _ |- _ =>
      rewrite IH; clear IH
    end.
  all: cbn in *; firstorder congruence.
Qed.

Lemma substitute_binders_alpha : forall b sigma x y z,
  (forall v, In v (free_vars b) -> v <> x -> ~ In y (free_vars (sigma v))) ->
  (forall v, In v (free_vars b) -> v <> x -> ~ In z (free_vars (sigma v))) ->
  alpha_eqb_in [y] [z]
    (substitute (bind_substitution sigma x y) b)
    (substitute (bind_substitution sigma x z) b) = true.
Proof.
  intros b sigma x y z Hy Hz.
  eapply alpha_substitute_in with (xs := []) (ys := []); [apply alpha_eqb_in_refl|].
  intros v w Hv Hw Hvw. apply Nat.eqb_eq in Hvw. subst w.
  unfold bind_substitution. destruct (v =? x) eqn:E.
  - cbn [alpha_eqb_in alpha_var]. now rewrite !Nat.eqb_refl.
  - apply Nat.eqb_neq in E. apply alpha_env_fresh;
      eauto using alpha_eqb_in_refl.
Qed.

Lemma substitute_bound_identity : forall b x,
  substitute (bind_substitution TVar x x) b = b.
Proof.
  intros b x. apply substitute_identity_on. intros v Hv.
  unfold bind_substitution. destruct (v =? x) eqn:E;
    [apply Nat.eqb_eq in E; now subst|reflexivity].
Qed.

Lemma alpha_rename_body : forall b x y,
  ~ In y (remove Nat.eq_dec x (free_vars b)) ->
  alpha_eqb_in [x] [y] b (subst (TVar y) x b) = true.
Proof.
  intros b x y Hfresh.
  rewrite <- (substitute_bound_identity b x) at 1.
  apply substitute_binders_alpha.
  - intros v Hv Hneq. cbn. intuition congruence.
  - intros v Hv Hneq [E|[]]. subst. apply Hfresh. now apply in_in_remove.
Qed.

Lemma alpha_rename_lam : forall b x y,
  ~ In y (remove Nat.eq_dec x (free_vars b)) ->
  alpha_equiv (TLam x b) (TLam y (subst (TVar y) x b)).
Proof. intros; now apply alpha_rename_body. Qed.

Lemma alpha_rename_pi : forall A B x y,
  ~ In y (remove Nat.eq_dec x (free_vars B)) ->
  alpha_equiv (TPi x A B) (TPi y A (subst (TVar y) x B)).
Proof.
  intros. unfold alpha_equiv, alpha_eqb. cbn [alpha_eqb_in].
  rewrite alpha_eqb_in_refl. now apply alpha_rename_body.
Qed.

Lemma alpha_rename_sigma : forall A B x y,
  ~ In y (remove Nat.eq_dec x (free_vars B)) ->
  alpha_equiv (TSigma x A B) (TSigma y A (subst (TVar y) x B)).
Proof.
  intros. unfold alpha_equiv, alpha_eqb. cbn [alpha_eqb_in].
  rewrite alpha_eqb_in_refl. now apply alpha_rename_body.
Qed.
