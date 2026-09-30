From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesCaseTyping.
Import ListNotations.

Definition term_domain t :=
  match t with TPi _ A _ | TSigma _ A _ => Some A | _ => None end.

Lemma typing_domain : forall Gamma t T,
  typing Gamma t T -> forall A, term_domain t = Some A -> type_wf Gamma A.
Proof.
  intros Gamma t T Htyping. induction Htyping; intros Z Hdom;
    cbn [term_domain] in Hdom; try discriminate;
    try solve [inversion Hdom; subst; eexists; eassumption | eauto].
  match goal with Ha : alpha_equiv ?tm ?un |- _ =>
    destruct tm; destruct un; cbn [term_domain] in Hdom; try discriminate;
    cbn [alpha_equiv alpha_eqb alpha_eqb_in] in Ha; try discriminate;
    apply Bool.andb_true_iff in Ha; destruct Ha as [HA HB]
  end.
  all: inversion Hdom; subst;
    match goal with IH : forall A, term_domain _ = Some A -> type_wf _ A |- _ =>
      destruct (IH _ eq_refl) as [k HK]
    end;
    exists k; eapply ty_alpha; eassumption.
Qed.

Lemma pi_domain_formation : forall Gamma x A B k,
  typing Gamma (TPi x A B) (TSort k) -> type_wf Gamma A.
Proof. intros; eapply typing_domain; [eassumption|reflexivity]. Qed.

Lemma subst_variable_identity : forall t x, subst (TVar x) x t = t.
Proof. exact substitute_bound_identity. Qed.

Lemma alpha_same_prefix : forall t xs x y,
  ~ In x (free_vars t) -> ~ In y (free_vars t) ->
  alpha_eqb_in (xs ++ [x]) (xs ++ [y]) t t = true.
Proof.
  intros t xs x y Hx Hy. eapply alpha_env_mono; [apply alpha_eqb_in_refl with (env := [])|].
  intros v w Hv Hw Heq. apply Nat.eqb_eq in Heq. subst w.
  induction xs as [|a xs IH]; cbn [app alpha_var].
  - destruct (v =? x) eqn:Ex; [apply Nat.eqb_eq in Ex; subst; contradiction|].
    destruct (v =? y) eqn:Ey; [apply Nat.eqb_eq in Ey; subst; contradiction|apply Nat.eqb_refl].
  - destruct (v =? a); auto.
Qed.

Section ContextTransport.
Variable weaken : forall Gamma x t A B k,
  fresh_in Gamma x -> typing Gamma t A -> typing Gamma B (TSort k) ->
  typing (extend Gamma x B) t A.
Variable regular : forall Gamma t A, typing Gamma t A -> type_wf Gamma A.
Variable preserve : forall Gamma t u A,
  typing Gamma t A -> reduction t u -> typing Gamma u A.

Lemma weaken_twice : forall Gamma x y A B t T j k,
  fresh_in Gamma x -> fresh_in Gamma y -> x <> y ->
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) -> typing Gamma t T ->
  typing (extend (extend Gamma x A) y B) t T.
Proof.
  intros Gamma x y A B t T j k Hx Hy Hxy HA HB Ht.
  eapply weaken.
  - unfold fresh_in. rewrite lookup_extend_other; assumption.
  - eapply weaken; eassumption.
  - eapply weaken; eassumption.
Qed.

Lemma arrow_apply_regular : forall Gamma A B f a,
  typing Gamma f (arrow A B) -> typing Gamma a A -> typing Gamma (TApp f a) B.
Proof.
  intros Gamma A B f a Hf Ha. destruct (regular _ _ _ Hf) as [k Hform].
  pose proof (@ty_app Gamma (fresh [A; B]) A B f a k Hform Hf Ha) as H.
  rewrite subst_fresh in H; [exact H|apply fresh_not_free; cbn; auto].
Qed.

Lemma exchange_typing : forall Gamma x y A B t T j k,
  fresh_in Gamma x -> fresh_in Gamma y -> x <> y ->
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  typing (extend Gamma y B) t T ->
  typing (extend (extend Gamma x A) y B) t T.
Proof.
  intros Gamma x y A B t T j k Hx Hy Hxy HA HB Ht.
  pose proof (typing_context _ _ _ HA) as Hctx.
  destruct (regular _ _ _ Ht) as [l HT].
  assert (Hpi : typing Gamma (TPi y B T) (TSort (Nat.max k l))) by (eapply ty_pi; eassumption).
  assert (Hlam : typing Gamma (TLam y t) (TPi y B T)) by (eapply ty_lam; eassumption).
  assert (Hy' : fresh_in (extend Gamma x A) y).
  { unfold fresh_in. rewrite lookup_extend_other; assumption. }
  assert (HB' : typing (extend Gamma x A) B (TSort k)) by (eapply weaken; eassumption).
  assert (Hpi' : typing (extend (extend Gamma x A) y B) (TPi y B T) (TSort (Nat.max k l))).
  { eapply weaken; [exact Hy'|eapply weaken; eassumption|exact HB']. }
  assert (Hlam' : typing (extend (extend Gamma x A) y B) (TLam y t) (TPi y B T)).
  { eapply weaken; [exact Hy'|eapply weaken; eassumption|exact HB']. }
  assert (Hvar : typing (extend (extend Gamma x A) y B) (TVar y) B).
  { apply ty_var; [eapply wf_cons; [eapply wf_cons| |]; eassumption|apply lookup_extend_same]. }
  pose proof (@ty_app _ y B T (TLam y t) (TVar y) _ Hpi' Hlam' Hvar) as Happ.
  rewrite subst_variable_identity in Happ.
  eapply preserve; [exact Happ|]. apply red_root. cbn [root_step].
  now rewrite subst_variable_identity.
Qed.

Lemma pi_coercion_typing : forall Gamma x y A B A' B' c d,
  fresh_in Gamma y -> type_wf Gamma (TPi x A B) -> type_wf Gamma (TPi y A' B') ->
  typing Gamma c (arrow A' A) ->
  typing (extend Gamma y A') d (arrow (coerced_codomain x y c B) B') ->
  typing Gamma (pi_coercion y c d) (arrow (TPi x A B) (TPi y A' B')).
Proof.
  intros Gamma x y A B A' B' c d Hy [j HS] [k HT] Hc Hd.
  destruct (pi_domain_formation _ _ _ _ _ HT) as [l HA'].
  destruct (exists_fresh_id Gamma [y]) as [f [Hf Hfy]].
  assert (Hneq : f <> y) by (cbn in Hfy; intuition congruence).
  assert (Hy' : fresh_in (extend Gamma f (TPi x A B)) y).
  { unfold fresh_in. rewrite lookup_extend_other; assumption. }
  assert (Hf' : fresh_in (extend Gamma y A') f).
  { unfold fresh_in. rewrite lookup_extend_other; [exact Hf|congruence]. }
  assert (Hfc : ~ In f (free_vars c)) by (eapply typing_fresh_not_free; eassumption).
  assert (Hfd : ~ In f (free_vars d)) by (eapply typing_fresh_not_free; eassumption).
  pose (f0 := fresh [c; d; TVar y]).
  assert (Hf0c : ~ In f0 (free_vars c)) by (apply fresh_not_free; cbn; tauto).
  assert (Hf0d : ~ In f0 (free_vars d)) by (apply fresh_not_free; cbn; tauto).
  assert (Hf0y : f0 <> y).
  { intro E. apply (fresh_not_free [c; d; TVar y] (TVar y) ltac:(cbn; tauto)). cbn; auto. }
  eapply ty_alpha with (t := TLam f (TLam y (TApp d (TApp (TVar f) (TApp c (TVar y)))))).
  - eapply arrow_intro; [exact weaken|exact HS|exact HT|exact Hf|].
    eapply ty_lam; [exact Hy'|eapply weaken; eassumption|].
    pose (Delta := extend (extend Gamma f (TPi x A B)) y A').
    assert (HDelta : wf Delta).
    { eapply wf_cons; [eapply wf_cons; eauto using typing_context|eapply weaken; eassumption|exact Hy']. }
    assert (Hd' : typing Delta d (arrow (coerced_codomain x y c B) B')).
    { eapply exchange_typing; eassumption. }
    eapply arrow_apply_regular; [exact Hd'|].
    eapply ty_app with (x := x) (A := A) (B := B) (k := j).
    + eapply weaken_twice; eassumption.
    + apply ty_var; [exact HDelta|]. unfold Delta.
      rewrite lookup_extend_other by congruence. apply lookup_extend_same.
    + eapply arrow_apply_regular.
      * eapply weaken_twice; eassumption.
      * apply ty_var; [exact HDelta|apply lookup_extend_same].
  - unfold pi_coercion, alpha_equiv, alpha_eqb. fold f0. cbn [alpha_eqb_in].
    repeat rewrite Bool.andb_true_iff. repeat split.
    + apply (alpha_same_prefix d [y] f f0); assumption.
    + cbn [alpha_var].
      assert (Ef : (f =? y) = false) by now apply Nat.eqb_neq.
      assert (Ef0 : (f0 =? y) = false) by now apply Nat.eqb_neq.
      now rewrite Ef, Ef0, !Nat.eqb_refl.
    + apply (alpha_same_prefix c [y] f f0); assumption.
    + cbn [alpha_var]. now rewrite Nat.eqb_refl.
Qed.

End ContextTransport.
