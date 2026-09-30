From Stdlib Require Import List Arith Bool Lia.
Require Import SubstitutionBase SubstitutionWork.
Import ListNotations.

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
