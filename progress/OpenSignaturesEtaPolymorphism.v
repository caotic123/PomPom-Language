(* A named counterexample to unrestricted eta subject reduction in the
   current calculus, including its function-cumulativity rule. This file
   imports no metatheory conjectures. *)
From Stdlib Require Import List Arith Bool Lia.
Require Import OpenSignaturesTypingEncoding.
Require nameless.DBEtaPolymorphism.
Import ListNotations.

Definition polymorphic_identity_type := TPi 0 (TSort 0) (TPi 1 (TVar 0) (TVar 0)).
Definition monomorphic_binding := TApp (TLam 1 (TLam 2 (TVar 1))) (TLam 3 (TVar 3)).
Definition polymorphic_eta := TLam 0 (TApp monomorphic_binding (TVar 0)).

Lemma empty_context_encoding : context_encoding [] [] empty_ctx.
Proof.
  constructor; cbn; auto using NoDup, wf_nil.
  - intros x; split; [cbn; tauto|reflexivity].
  - intros n A H; destruct n; discriminate.
Qed.

Theorem polymorphic_eta_typing : typing empty_ctx polymorphic_eta polymorphic_identity_type.
Proof.
  eapply typing_reflection_given.
  - exact nameless.DBEtaPolymorphism.polymorphic_eta_typing.
  - exact empty_context_encoding.
  - reflexivity.
  - reflexivity.
Qed.

Theorem polymorphic_eta_reduction : reduction polymorphic_eta monomorphic_binding.
Proof. apply red_eta; cbn; intuition discriminate. Qed.

Theorem monomorphic_binding_not_polymorphic :
  ~ typing empty_ctx monomorphic_binding polymorphic_identity_type.
Proof.
  intro H.
  pose proof (typing_encoding _ _ _ H _ _ empty_context_encoding ST.wf_nil) as HDB.
  exact (nameless.DBEtaPolymorphism.monomorphic_binding_not_polymorphic _ _ HDB).
Qed.

Theorem unrestricted_eta_counterexample :
  typing empty_ctx polymorphic_eta polymorphic_identity_type /\
  reduction polymorphic_eta monomorphic_binding /\
  ~ typing empty_ctx monomorphic_binding polymorphic_identity_type.
Proof.
  split; [exact polymorphic_eta_typing|].
  split; [exact polymorphic_eta_reduction|exact monomorphic_binding_not_polymorphic].
Qed.

Theorem full_preservation_refuted :
  ~ (forall Gamma t u A,
    typing Gamma t A -> reduction t u -> typing Gamma u A).
Proof.
  intro H; apply monomorphic_binding_not_polymorphic.
  eapply H; [exact polymorphic_eta_typing|exact polymorphic_eta_reduction].
Qed.

Print Assumptions unrestricted_eta_counterexample.
Print Assumptions full_preservation_refuted.
