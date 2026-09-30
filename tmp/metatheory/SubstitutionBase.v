From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesBinding.
Import ListNotations.

Local Ltac membership :=
  cbn in *; repeat rewrite in_app_iff in *;
  repeat rewrite in_remove_iff in *; intuition eauto using in_or_app.

Lemma alpha_env_mono : forall t u xs ys xs' ys',
  alpha_eqb_in xs ys t u = true ->
  (forall x y, In x (free_vars t) -> In y (free_vars u) ->
    alpha_var xs ys x y = true -> alpha_var xs' ys' x y = true) ->
  alpha_eqb_in xs' ys' t u = true.
Proof.
  induction t; destruct u; intros xs ys xs' ys' Ha Henv;
    cbn [alpha_eqb_in] in *; try discriminate;
    repeat rewrite Bool.andb_true_iff in *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try solve [reflexivity | assumption | apply Henv; cbn; auto].
  all: repeat split; try assumption;
    match goal with
    | IH : forall u xs ys xs' ys', alpha_eqb_in xs ys ?tm u = true -> _,
      Ha : alpha_eqb_in ?xs ?ys ?tm ?un = true
      |- alpha_eqb_in ?xs' ?ys' ?tm ?un = true =>
        eapply (IH un xs ys xs' ys' Ha)
    end.
  all: intros v w Hv Hw Hav;
    try solve [apply Henv; [membership|membership|exact Hav]].
  all: cbn in Hav |- *;
    destruct (v =? x) eqn:Ev; destruct (w =? x0) eqn:Ew;
    try discriminate; try reflexivity;
    apply Nat.eqb_neq in Ev, Ew; apply Henv; [membership|membership|exact Hav].
Qed.

Lemma alpha_env_fresh : forall t u xs ys x y,
  alpha_eqb_in xs ys t u = true ->
  ~ In x (free_vars t) -> ~ In y (free_vars u) ->
  alpha_eqb_in (x :: xs) (y :: ys) t u = true.
Proof.
  intros t u xs ys x y Ha Hx Hy. eapply alpha_env_mono; [exact Ha|].
  intros v w Hv Hw Hav. cbn.
  destruct (v =? x) eqn:Ev; [apply Nat.eqb_eq in Ev; subst; contradiction|].
  destruct (w =? y) eqn:Ew; [apply Nat.eqb_eq in Ew; subst; contradiction|].
  exact Hav.
Qed.

Lemma alpha_closed_context : forall t u xs,
  alpha_equiv t u -> alpha_eqb_in xs xs t u = true.
Proof.
  intros t u xs Ha. eapply alpha_env_mono; [exact Ha|].
  intros x y Hx Hy Hxy. apply Nat.eqb_eq in Hxy. subst. apply alpha_var_refl.
Qed.

Lemma substitution_binder_fresh : forall sigma x b v,
  In v (free_vars b) -> v <> x ->
  ~ In (substitution_binder sigma x b) (free_vars (sigma v)).
Proof.
  intros sigma x b v Hv Hneq. unfold substitution_binder.
  set (avoid := flat_map (fun y => free_vars (sigma y))
    (remove Nat.eq_dec x (free_vars b))).
  assert (Hin : forall a, In a (free_vars (sigma v)) -> In a avoid).
  { intros a Ha. apply in_flat_map. exists v. split; [apply in_in_remove; assumption|exact Ha]. }
  destruct (existsb (Nat.eqb x) avoid) eqn:E; intros Ha.
  - apply (fresh_id_not_in (vars b ++ avoid ++ [x])).
    apply in_or_app; right. apply in_or_app; left. now apply Hin.
  - apply Hin in Ha. assert (Ex : existsb (Nat.eqb x) avoid = true).
    { apply existsb_exists. exists x. split; [exact Ha|apply Nat.eqb_refl]. }
    congruence.
Qed.

Lemma alpha_substitute_in : forall t u xs ys ms ns sigma tau,
  alpha_eqb_in xs ys t u = true ->
  (forall x y, In x (free_vars t) -> In y (free_vars u) ->
    alpha_var xs ys x y = true -> alpha_eqb_in ms ns (sigma x) (tau y) = true) ->
  alpha_eqb_in ms ns (substitute sigma t) (substitute tau u) = true.
Proof.
  induction t; destruct u; intros xs ys ms ns sigma tau Ha Hmap;
    cbn [alpha_eqb_in] in Ha; try discriminate;
    repeat rewrite Bool.andb_true_iff in Ha;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    cbn [substitute alpha_eqb_in]; repeat rewrite Bool.andb_true_iff;
    try solve [reflexivity | assumption | apply Hmap; cbn; auto].
  all: repeat split; try assumption;
    match goal with
    | IH : forall u xs ys ms ns sigma tau, alpha_eqb_in xs ys ?tm u = true -> _,
      Ha : alpha_eqb_in ?xs ?ys ?tm ?un = true
      |- alpha_eqb_in ?ms ?ns (substitute ?sigma ?tm) (substitute ?tau ?un) = true =>
        eapply (IH un xs ys ms ns sigma tau Ha)
    end.
  all: intros v w Hv Hw Hav;
    try solve [apply Hmap; [membership|membership|exact Hav]].
  all: cbn [alpha_var] in Hav; unfold bind_substitution;
    destruct (v =? x) eqn:Ev; destruct (w =? x0) eqn:Ew;
    try discriminate;
    [cbn [alpha_eqb_in alpha_var]; rewrite !Nat.eqb_refl; reflexivity|].
  all: apply Nat.eqb_neq in Ev, Ew;
    apply alpha_env_fresh;
    [apply Hmap; [membership|membership|exact Hav]|
      eapply substitution_binder_fresh; eassumption|
      eapply substitution_binder_fresh; eassumption].
Qed.

Lemma substitute_alpha : forall t u sigma tau,
  alpha_equiv t u ->
  (forall x, In x (free_vars t) -> alpha_equiv (sigma x) (tau x)) ->
  alpha_equiv (substitute sigma t) (substitute tau u).
Proof.
  intros t u sigma tau Ha Hmap. eapply alpha_substitute_in; [exact Ha|].
  intros x y Hx Hy Hxy. apply Nat.eqb_eq in Hxy. subst. now apply Hmap.
Qed.

