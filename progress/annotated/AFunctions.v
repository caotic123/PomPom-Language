(* Small derived constructors keep annotated examples and operator rules short. *)
From Stdlib Require Import List Arith.
Require Export annotated.ASubstitution.
Import ListNotations.

Lemma arrow_formation : forall Gamma A B j k,
  typing Gamma A (Raw.TSort j) -> typing Gamma B (Raw.TSort k) ->
  typing Gamma (arrow A B) (Raw.TSort (Nat.max j k)).
Proof.
  intros Gamma A B j k HA HB; unfold arrow; eapply ty_pi; [exact HA|].
  exact (weakening _ _ _ _ _ HB (typing_erasure _ _ _ HA)).
Qed.

Definition identity A := TLam A (lift 1 0 A) (TVar 0).
Definition constant A B t := TLam B (lift 1 0 A) (lift 1 0 t).
Definition k_combinator A B :=
  TLam A (arrow (lift 1 0 B) (lift 1 0 A))
    (constant (lift 1 0 A) (lift 1 0 B) (TVar 0)).
Definition arrow_apply A B f a := TApp A (lift 1 0 B) f a.

Lemma identity_typing : forall Gamma A k,
  typing Gamma A (Raw.TSort k) ->
  typing Gamma (identity A) (Raw.arrow (erase A) (erase A)).
Proof.
  intros Gamma A k HA; unfold identity, Raw.arrow.
  rewrite <- erase_lift; eapply ty_lam; [exact HA| |].
  - exact (weakening _ _ _ _ _ HA (typing_erasure _ _ _ HA)).
  - rewrite erase_lift; eapply ty_var;
      [eapply RT.wf_cons; eauto using typing_context, typing_erasure|reflexivity].
Qed.

Lemma constant_typing : forall Gamma A B t j k,
  typing Gamma A (Raw.TSort j) -> typing Gamma B (Raw.TSort k) ->
  typing Gamma t (erase A) ->
  typing Gamma (constant A B t) (Raw.arrow (erase B) (erase A)).
Proof.
  intros Gamma A B t j k HA HB Ht; unfold constant, Raw.arrow.
  rewrite <- erase_lift; eapply ty_lam; [exact HB| |].
  - exact (weakening _ _ _ _ _ HA (typing_erasure _ _ _ HB)).
  - rewrite erase_lift; exact (weakening _ _ _ _ _ Ht (typing_erasure _ _ _ HB)).
Qed.

Lemma k_combinator_typing : forall Gamma A B j k,
  typing Gamma A (Raw.TSort j) -> typing Gamma B (Raw.TSort k) ->
  typing Gamma (k_combinator A B)
    (Raw.arrow (erase A) (Raw.arrow (erase B) (erase A))).
Proof.
  intros Gamma A B j k HA HB.
  pose proof (weakening _ _ _ _ _ HA (typing_erasure _ _ _ HA)) as HA'.
  pose proof (weakening _ _ _ _ _ HB (typing_erasure _ _ _ HA)) as HB'.
  unfold k_combinator; unfold Raw.arrow at 1; rewrite RW.lift_arrow.
  rewrite <- !erase_lift, <- erase_arrow.
  eapply ty_lam; [exact HA|eapply arrow_formation; eassumption|].
  rewrite erase_arrow; eapply constant_typing; [exact HA'|exact HB'|].
  rewrite erase_lift; eapply ty_var;
    [eapply RT.wf_cons; eauto using typing_context, typing_erasure|reflexivity].
Qed.

Lemma arrow_application : forall Gamma A B f a j k,
  typing Gamma A (Raw.TSort j) -> typing Gamma B (Raw.TSort k) ->
  typing Gamma f (Raw.arrow (erase A) (erase B)) -> typing Gamma a (erase A) ->
  typing Gamma (arrow_apply A B f a) (erase B).
Proof.
  intros Gamma A B f a j k HA HB Hf Ha; unfold arrow_apply.
  replace (erase B) with (Raw.subst (erase a) 0 (erase (lift 1 0 B)))
    by (rewrite erase_lift; apply RB.subst_lift_zero).
  eapply ty_app; [exact HA| | |exact Ha].
  - exact (weakening _ _ _ _ _ HB (typing_erasure _ _ _ HA)).
  - rewrite erase_lift; exact Hf.
Qed.
