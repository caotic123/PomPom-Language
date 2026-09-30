(* Binding and scoping facts for the named calculus. All proofs in this
   module use only the syntax, alpha relation, and declarative typing rules;
   none imports the metatheory conjectures. *)
From Stdlib Require Import List Arith Bool String Lia FMapFacts.
Require Export OpenSignaturesCore.
Import ListNotations.

Lemma in_remove_iff : forall x y xs,
  In x (remove Nat.eq_dec y xs) <-> In x xs /\ x <> y.
Proof. intros; split; [apply in_remove | intros []; now apply in_in_remove]. Qed.

Lemma flat_map_ext_on : forall (A B : Type) (xs : list A) (f g : A -> list B),
  (forall x, In x xs -> f x = g x) -> flat_map f xs = flat_map g xs.
Proof.
  intros A B xs; induction xs; intros f g H; cbn; [reflexivity|].
  rewrite H by (cbn; auto). f_equal. apply IHxs. intros; apply H; cbn; auto.
Qed.

Local Ltac membership :=
  cbn in *; repeat rewrite in_app_iff in *;
  repeat rewrite in_remove_iff in *; intuition eauto using in_or_app.

Lemma free_vars_in_vars : forall t x, In x (free_vars t) -> In x (vars t).
Proof. induction t; intros v H; cbn [free_vars vars] in *; membership. Qed.

Lemma substitution_binder_ext : forall sigma tau x b,
  (forall v, In v (remove Nat.eq_dec x (free_vars b)) -> sigma v = tau v) ->
  substitution_binder sigma x b = substitution_binder tau x b.
Proof.
  intros sigma tau x b H. unfold substitution_binder.
  assert (E : flat_map (fun v => free_vars (sigma v))
    (remove Nat.eq_dec x (free_vars b)) =
    flat_map (fun v => free_vars (tau v)) (remove Nat.eq_dec x (free_vars b))).
  { apply flat_map_ext_on. intros; now rewrite H. }
  now rewrite E.
Qed.

Lemma substitution_binder_identity : forall sigma x b,
  (forall v, In v (remove Nat.eq_dec x (free_vars b)) -> sigma v = TVar v) ->
  substitution_binder sigma x b = x.
Proof.
  intros sigma x b H. unfold substitution_binder.
  destruct (existsb (Nat.eqb x) _) eqn:E; [|reflexivity].
  apply existsb_exists in E. destruct E as [v [Hin Heq]].
  apply Nat.eqb_eq in Heq. subst v.
  apply in_flat_map in Hin. destruct Hin as [v [Hv Hin]].
  rewrite H in Hin by assumption. cbn in Hin. destruct Hin as [<-|[]].
  exfalso. exact (remove_In Nat.eq_dec _ _ Hv).
Qed.

Local Ltac substitution_ih H :=
  match goal with
  | IH : forall sigma tau, _ -> substitute sigma ?tm = substitute tau ?tm
    |- substitute _ ?tm = substitute _ ?tm =>
      apply IH; intros; apply H; membership
  | IH : forall sigma, _ -> substitute sigma ?tm = ?tm
    |- substitute _ ?tm = ?tm =>
      apply IH; intros; apply H; membership
  end.

Lemma substitute_ext_on : forall t sigma tau,
  (forall v, In v (free_vars t) -> sigma v = tau v) ->
  substitute sigma t = substitute tau t.
Proof.
  induction t; intros sigma tau H; cbn [substitute free_vars] in *;
    try solve [reflexivity | apply H; cbn; auto | f_equal; substitution_ih H].
  all: rewrite (substitution_binder_ext sigma tau) by
    (intros; apply H; membership).
  all: f_equal; try solve [substitution_ih H]; apply IHt || apply IHt2.
  all: intros v Hv; unfold bind_substitution;
    destruct (v =? x) eqn:E; [reflexivity|];
    apply Nat.eqb_neq in E; apply H; membership.
Qed.

Lemma substitute_identity_on : forall t sigma,
  (forall v, In v (free_vars t) -> sigma v = TVar v) -> substitute sigma t = t.
Proof.
  induction t; intros sigma H; cbn [substitute free_vars] in *;
    try solve [reflexivity | apply H; cbn; auto | f_equal; substitution_ih H].
  all: rewrite substitution_binder_identity by
    (intros; apply H; membership).
  all: f_equal; try solve [substitution_ih H]; apply IHt || apply IHt2.
  all: intros v Hv; unfold bind_substitution;
    destruct (v =? x) eqn:E; [apply Nat.eqb_eq in E; now subst|];
    apply Nat.eqb_neq in E; apply H; membership.
Qed.

Lemma subst_fresh : forall t u x,
  ~ In x (free_vars t) -> subst u x t = t.
Proof.
  intros t u x H. apply substitute_identity_on. intros v Hv.
  destruct (v =? x) eqn:E; [apply Nat.eqb_eq in E; subst; contradiction|reflexivity].
Qed.

Lemma subst_fresh_vars : forall t u x,
  ~ In x (vars t) -> subst u x t = t.
Proof. intros; apply subst_fresh; eauto using free_vars_in_vars. Qed.

Lemma alpha_var_free : forall xs ys x y,
  alpha_var xs ys x y = true -> ~ In x xs -> x = y /\ ~ In y ys.
Proof.
  induction xs as [|a xs IH]; destruct ys as [|b ys];
    intros x y H Hfree; cbn in *; try discriminate.
  - apply Nat.eqb_eq in H; auto.
  - destruct (x =? a) eqn:Ex; [apply Nat.eqb_eq in Ex; subst; tauto|].
    destruct (y =? b) eqn:Ey; [discriminate|].
    apply Nat.eqb_neq in Ey. specialize (IH _ _ _ H ltac:(tauto)). intuition congruence.
Qed.

Lemma alpha_free_vars_in : forall t u xs ys x,
  alpha_eqb_in xs ys t u = true ->
  In x (free_vars t) -> ~ In x xs -> In x (free_vars u) /\ ~ In x ys.
Proof.
  induction t; destruct u; intros xs ys v H Hin Hfree;
    cbn [alpha_eqb_in] in H; try discriminate;
    repeat rewrite Bool.andb_true_iff in H;
    cbn [free_vars] in *.
  all: try solve [destruct Hin as [<-|[]];
    destruct (alpha_var_free _ _ _ _ H Hfree); subst; cbn; auto].
  all: repeat rewrite in_app_iff in *; repeat rewrite in_remove_iff in *.
  all: repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    | H : _ \/ _ |- _ => destruct H
    end; try contradiction.
  all: match goal with
    | IH : forall u xs ys x, alpha_eqb_in xs ys ?tm u = true -> _,
      Ha : alpha_eqb_in ?xs ?ys ?tm ?un = true,
      Hf : In ?v (free_vars ?tm) |- _ =>
        pose proof (IH un xs ys v Ha Hf ltac:(cbn; intuition congruence))
    end.
  all: cbn in *; repeat rewrite in_remove_iff in *; intuition congruence.
Qed.

Lemma alpha_free_vars : forall t u,
  alpha_equiv t u -> forall x, In x (free_vars t) <-> In x (free_vars u).
Proof.
  intros t u H x; split; intro Hin.
  - exact (proj1 (alpha_free_vars_in t u [] [] x H Hin ltac:(cbn; tauto))).
  - apply alpha_eqb_in_sym in H.
    exact (proj1 (alpha_free_vars_in u t [] [] x H Hin ltac:(cbn; tauto))).
Qed.

Module BindingMapFacts := FMapFacts.WFacts(VarMap).

Lemma lookup_extend_same : forall Gamma x A, lookup (extend Gamma x A) x = Some A.
Proof. intros; apply BindingMapFacts.add_eq_o; reflexivity. Qed.

Lemma lookup_extend_other : forall Gamma x y A,
  x <> y -> lookup (extend Gamma x A) y = lookup Gamma y.
Proof. intros; now apply BindingMapFacts.add_neq_o. Qed.

Definition scoped Gamma t := forall x, In x (free_vars t) ->
  exists A, lookup Gamma x = Some A.

Lemma scoped_extend : forall Gamma binder A tm,
  scoped (extend Gamma binder A) tm ->
  forall x, In x (remove Nat.eq_dec binder (free_vars tm)) ->
  exists B, lookup Gamma x = Some B.
Proof.
  intros Gamma binder A tm H x Hin. apply in_remove in Hin.
  destruct Hin as [Hin Hneq]. destruct (H x Hin) as [B HB].
  exists B. rewrite lookup_extend_other in HB by congruence. exact HB.
Qed.

Lemma typing_scoped : forall Gamma t A, typing Gamma t A -> scoped Gamma t.
Proof.
  intros Gamma t A H. induction H; unfold scoped in *;
    intros v Hv; cbn [free_vars] in Hv;
    repeat rewrite in_app_iff in Hv;
    repeat match type of Hv with _ \/ _ => destruct Hv as [Hv|Hv] end;
    try contradiction; eauto using scoped_extend.
  - destruct Hv as [<-|[]]. eauto.
  - apply IHtyping. now apply (proj2 (alpha_free_vars _ _ H0 v)).
Qed.

Lemma typing_fresh_not_free : forall Gamma t A x,
  typing Gamma t A -> fresh_in Gamma x -> ~ In x (free_vars t).
Proof.
  intros Gamma t A x Hty Hfresh Hin.
  destruct (typing_scoped _ _ _ Hty x Hin) as [B HB].
  unfold fresh_in in Hfresh. congruence.
Qed.

Lemma wf_lookup_scoped : forall Gamma,
  wf Gamma -> forall x A, lookup Gamma x = Some A -> scoped Gamma A.
Proof.
  intros Gamma Hwf; induction Hwf; intros y B Hlookup.
  - discriminate Hlookup.
  - destruct (Nat.eq_dec x y) as [->|Hneq].
    + rewrite lookup_extend_same in Hlookup. inversion Hlookup; subst.
      intros v Hv. destruct (typing_scoped _ _ _ H v Hv) as [C HC].
      exists C. rewrite lookup_extend_other; [exact HC|].
      intro E; subst. unfold fresh_in in H0. congruence.
    + rewrite lookup_extend_other in Hlookup by exact Hneq.
      intros v Hv. destruct (IHHwf _ _ Hlookup v Hv) as [C HC].
      exists C. rewrite lookup_extend_other; [exact HC|].
      intro E; subst. unfold fresh_in in H0. congruence.
Qed.

Lemma wf_type_fresh_not_free : forall Gamma v A x,
  wf Gamma -> lookup Gamma v = Some A -> fresh_in Gamma x ->
  ~ In x (free_vars A).
Proof.
  intros Gamma v A x Hwf Hlookup Hfresh Hin.
  destruct (wf_lookup_scoped _ Hwf _ _ Hlookup _ Hin) as [B HB].
  unfold fresh_in in Hfresh. congruence.
Qed.

Lemma fresh_id_not_in : forall ids, ~ In (fresh_id ids) ids.
Proof.
  assert (Hmax : forall ids n, In n ids -> n <= fold_right Nat.max 0 ids).
  {
    intros ids. induction ids as [|a ids IH]; intros n Hin; simpl in *.
    - contradiction.
    - destruct Hin as [<- | Hin].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
  }
  intros ids Hin. apply Hmax in Hin.
  unfold fresh_id in Hin.
  exact (Nat.nle_succ_diag_l _ Hin).
Qed.

(* Supply any context and any additional IDs to avoid. *)
Lemma exists_fresh_id : forall (Gamma : ctx) (ids : list nat),
  exists z, fresh_in Gamma z /\ ~ In z ids.
Proof.
  intros Gamma ids.
  pose (context_ids := flat_map
    (fun entry => fst entry :: vars (snd entry)) (VarMap.elements Gamma)).
  pose (z := fresh_id (ids ++ context_ids)).
  assert (Hz : ~ In z (ids ++ context_ids)) by apply fresh_id_not_in.
  exists z. split.
  - unfold fresh_in, lookup.
    destruct (VarMap.find z Gamma) as [D |] eqn:Hfind; [|reflexivity].
    exfalso. apply Hz. apply in_or_app. right.
    apply VarMap.find_2 in Hfind.
    apply VarMap.elements_1 in Hfind.
    apply InA_alt in Hfind.
    destruct Hfind as [[q T] [[Hkey Hvalue] Hin]].
    change (z = q) in Hkey.
    unfold context_ids. apply in_flat_map.
    exists (q, T). split; [exact Hin |].
    simpl. left. symmetry. exact Hkey.
  - intro Hin. apply Hz. apply in_or_app. left. exact Hin.
Qed.

