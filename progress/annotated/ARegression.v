(* The old counterexample keeps its typing, but its annotations expose the
   dependency that makes contraction illegal. Independent safe eta examples
   check that general contraction, including applications, remains present. *)
From Stdlib Require Import List Arith.
Require Import annotated.AFunctions annotated.AEta annotated.ABeta.
Require nameless.DBEtaPolymorphism.
Import ListNotations.
Module Old := nameless.DBEtaPolymorphism.

Definition local_identity_type := arrow (TVar 0) (TVar 0).
Definition annotated_binding :=
  arrow_apply local_identity_type (arrow (TSort 0) local_identity_type)
    (k_combinator local_identity_type (TSort 0)) (identity (TVar 0)).
Definition annotated_source :=
  TLam (TSort 0) local_identity_type
    (arrow_apply (TSort 0) local_identity_type annotated_binding (TVar 0)).

Lemma annotated_binding_erasure : erase annotated_binding = Old.monomorphic_binding.
Proof. reflexivity. Qed.

Lemma annotated_source_erasure : erase annotated_source = Old.polymorphic_eta.
Proof. reflexivity. Qed.

Theorem annotated_source_typing :
  typing [] annotated_source Old.polymorphic_identity_type.
Proof.
  assert (HW : RT.wf [Raw.TSort 0]) by
    (eapply RT.wf_cons; [constructor|apply RT.ty_sort; constructor]).
  assert (HA : typing [Raw.TSort 0] (TVar 0) (Raw.TSort 0)).
  { exact (ty_var _ 0 _ HW eq_refl). }
  assert (HAA : typing [Raw.TSort 0] local_identity_type (Raw.TSort 0)).
  { exact (arrow_formation _ _ _ 0 0 HA HA). }
  assert (HS : typing [Raw.TSort 0] (TSort 0) (Raw.TSort 1)) by now apply ty_sort.
  assert (HF : typing [Raw.TSort 0] annotated_binding
    (Raw.arrow (Raw.TSort 0) (erase local_identity_type))).
  { change (typing [Raw.TSort 0] annotated_binding
      (erase (arrow (TSort 0) local_identity_type))).
    unfold annotated_binding.
    eapply arrow_application; [exact HAA| | |].
    - exact (arrow_formation _ _ _ 1 0 HS HAA).
    - rewrite erase_arrow; eapply k_combinator_typing; eassumption.
    - exact (identity_typing _ _ 0 HA). }
  unfold annotated_source, Old.polymorphic_identity_type.
  change (typing [] (TLam (TSort 0) local_identity_type
    (arrow_apply (TSort 0) local_identity_type annotated_binding (TVar 0)))
    (Raw.TPi (erase (TSort 0)) (erase local_identity_type))).
  eapply ty_lam; [apply ty_sort; constructor|exact HAA|].
  eapply arrow_application; eassumption.
Qed.

Theorem hidden_dependency_visible : occurs 0 annotated_binding = true.
Proof. reflexivity. Qed.

Theorem bad_eta_rejected : eta_contract annotated_source = None.
Proof. reflexivity. Qed.

Theorem bad_eta_has_no_root : forall u, ~ eta_root annotated_source u.
Proof.
  intros u H; pose proof (eta_contract_complete _ _ H) as HC.
  rewrite bad_eta_rejected in HC; discriminate.
Qed.

Definition safe_application :=
  arrow_apply TUnitT (arrow TUnitT TUnitT) (TVar 0) TUnit.
Definition safe_eta_source := TLam TUnitT TUnitT
  (arrow_apply TUnitT TUnitT (lift 1 0 safe_application) (TVar 0)).

Theorem application_eta_allowed : eta_contract safe_eta_source = Some safe_application.
Proof. reflexivity. Qed.

Theorem general_eta_allowed : forall A B C D f,
  eta_contract (TLam A B (TApp C D (lift 1 0 f) (TVar 0))) = Some f.
Proof. intros; apply eta_contract_complete; constructor. Qed.

Theorem annotation_erasure_is_not_eta_freshness :
  erase annotated_source = Old.polymorphic_eta /\
  typing [] annotated_source Old.polymorphic_identity_type /\
  eta_contract annotated_source = None /\
  nameless.DBCore.reduction (erase annotated_source) (erase annotated_binding).
Proof.
  split; [reflexivity|]. split; [exact annotated_source_typing|].
  split; [reflexivity|]. rewrite annotated_source_erasure, annotated_binding_erasure.
  apply nameless.DBCore.red_eta.
Qed.

Print Assumptions annotated_source_typing.
Print Assumptions bad_eta_has_no_root.
Print Assumptions annotation_erasure_is_not_eta_freshness.
