(* Capture-avoiding simultaneous substitution, with composition and binder
   renaming up to alpha equivalence. This module imports no conjectures. *)
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

Lemma composition_image_fresh : forall sigma tau x b v,
  In v (free_vars b) -> v <> x ->
  ~ In
    (substitution_binder sigma (substitution_binder tau x b)
      (substitute (bind_substitution tau x (substitution_binder tau x b)) b))
    (free_vars (substitute sigma (tau v))).
Proof.
  intros sigma tau x b v Hv Hneq Hin.
  apply free_vars_substitute in Hin. destruct Hin as [q [Hq Hw]].
  assert (Hqneq : q <> substitution_binder tau x b).
  { intro E. subst q. exact (substitution_binder_fresh tau x b v Hv Hneq Hq). }
  assert (Hbody : In q (free_vars
    (substitute (bind_substitution tau x (substitution_binder tau x b)) b))).
  { apply free_vars_substitute. exists v. split; [exact Hv|].
    unfold bind_substitution. destruct (v =? x) eqn:E;
      [apply Nat.eqb_eq in E; contradiction|exact Hq]. }
  exact (substitution_binder_fresh sigma (substitution_binder tau x b)
    (substitute (bind_substitution tau x (substitution_binder tau x b)) b)
    q Hbody Hqneq Hw).
Qed.

Lemma composition_under_binder : forall b,
  (forall sigma tau, alpha_equiv
    (substitute sigma (substitute tau b))
    (substitute (fun v => substitute sigma (tau v)) b)) ->
  forall sigma tau x,
  let z := substitution_binder tau x b in
  let b' := substitute (bind_substitution tau x z) b in
  let w := substitution_binder sigma z b' in
  let r := substitution_binder (fun v => substitute sigma (tau v)) x b in
  alpha_eqb_in [w] [r]
    (substitute (bind_substitution sigma z w) b')
    (substitute (bind_substitution (fun v => substitute sigma (tau v)) x r) b) = true.
Proof.
  intros b IH sigma tau x z b' w r.
  eapply alpha_eqb_in_trans with (zs := [w]).
  - apply alpha_closed_context, IH.
  - eapply alpha_substitute_in with (xs := []) (ys := []);
      [apply alpha_eqb_in_refl|].
    intros v q Hv Hq Heq. apply Nat.eqb_eq in Heq. subst q.
    unfold bind_substitution at 2 3. destruct (v =? x) eqn:E.
    + cbn [substitute]. unfold bind_substitution. rewrite Nat.eqb_refl.
      cbn [alpha_eqb_in alpha_var]. now rewrite !Nat.eqb_refl.
    + apply Nat.eqb_neq in E.
      assert (Hsame : substitute (bind_substitution sigma z w) (tau v) =
        substitute sigma (tau v)).
      { apply substitute_ext_on. intros q Hq'. unfold bind_substitution.
        destruct (q =? z) eqn:Eq; [|reflexivity].
        apply Nat.eqb_eq in Eq. subst q. exfalso.
        exact (substitution_binder_fresh tau x b v Hv E Hq'). }
      rewrite Hsame. apply alpha_env_fresh; [apply alpha_eqb_in_refl| |].
      * exact (composition_image_fresh sigma tau x b v Hv E).
      * exact (substitution_binder_fresh
          (fun q => substitute sigma (tau q)) x b v Hv E).
Qed.

Theorem substitute_compose : forall t sigma tau,
  alpha_equiv (substitute sigma (substitute tau t))
    (substitute (fun v => substitute sigma (tau v)) t).
Proof.
  induction t; intros sigma tau;
    cbn [substitute]; unfold alpha_equiv, alpha_eqb in *;
    cbn [alpha_eqb_in]; repeat rewrite Bool.andb_true_iff;
    repeat split; try apply alpha_eqb_in_refl;
    try apply Nat.eqb_refl; try apply String.eqb_refl; try reflexivity;
    try apply IHt; try apply IHt1; try apply IHt2; try apply IHt3;
    try apply IHt4; try apply IHt5; try apply IHt6; try apply IHt7.
  all: apply composition_under_binder; assumption.
Qed.
