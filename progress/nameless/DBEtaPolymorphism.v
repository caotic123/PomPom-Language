(* An application with a monomorphic local binding cannot acquire the
   polymorphic type available to its eta expansion. *)
From Stdlib Require Import List Arith Bool Lia.
Require Import nameless.DBEtaPrincipal.
Import ListNotations.

Lemma comparison_unit_source : forall A,
  type_comparison TUnitT A -> conv TUnitT A.
Proof.
  intros A H; inversion H; subst; auto.
  all: exfalso; pose proof (conversion_head _ _ _ _ H0 eq_refl eq_refl); discriminate.
Qed.

Lemma comparison_sort_unit_impossible : forall k,
  ~ type_comparison (TSort k) TUnitT.
Proof.
  intros k H; inversion H; subst.
  - pose proof (conversion_head _ _ _ _ H0 eq_refl eq_refl); discriminate.
  - pose proof (conversion_head _ _ _ _ H1 eq_refl eq_refl); discriminate.
  - pose proof (conversion_head _ _ _ _ H0 eq_refl eq_refl); discriminate.
Qed.

Lemma no_constant_polymorphic_identity : forall A,
  ~ type_comparison (lift 1 0 A) (TPi (TVar 0) (TVar 1)).
Proof.
  intros A H.
  pose proof (comparison_subst _ _ H TUnitT 0) as HU.
  pose proof (comparison_subst _ _ H (TSort 0) 0) as HS.
  rewrite subst_lift_cancel in HU, HS; cbn [subst lift] in HU, HS.
  destruct (comparison_pi_source _ _ HU _ _ (cv_refl _)) as [C [D HC]].
  assert (HU' : type_comparison (TPi C D) (TPi TUnitT TUnitT)).
  { eapply comparison_left_conversion; [exact HU|now apply cv_sym]. }
  assert (HS' : type_comparison (TPi C D) (TPi (TSort 0) (TSort 0))).
  { eapply comparison_left_conversion; [exact HS|now apply cv_sym]. }
  destruct (comparison_pi_inversion _ _ _ _ HU') as [HUC _].
  destruct (comparison_pi_inversion _ _ _ _ HS') as [HSC _].
  apply comparison_unit_source in HUC.
  apply (comparison_sort_unit_impossible 0).
  eapply comparison_right_conversion; [exact HSC|now apply cv_sym].
Qed.

Definition polymorphic_identity_type := TPi (TSort 0) (TPi (TVar 0) (TVar 1)).
Definition monomorphic_binding := TApp (TLam (TLam (TVar 1))) (TLam (TVar 0)).
Definition polymorphic_eta := TLam (TApp (lift 1 0 monomorphic_binding) (TVar 0)).

Theorem monomorphic_binding_not_polymorphic : forall Gamma a,
  ~ typing Gamma (TApp (TLam (TLam (TVar 1))) a) polymorphic_identity_type.
Proof.
  intros Gamma a H.
  destruct (application_change_generation _ _ _ H _ _ eq_refl)
    as [U [V [Hf [Ha Hout]]]].
  destruct (lambda_generation _ _ _ Hf _ eq_refl)
    as [C [D [j [HP [Hb HC]]]]].
  destruct (conversion_pi _ _ _ _ HC) as [_ HDV].
  destruct (lambda_generation _ _ _ Hb _ eq_refl)
    as [E [F [k [HQ [Hz HEF]]]]].
  destruct (variable_change_generation _ _ _ Hz _ eq_refl) as [C' [HC' HCF]].
  cbn [nth_error] in HC'; inversion HC'; subst C'.
  assert (Hresult : type_comparison
    (TPi (subst a 0 E) (subst a 1 F)) polymorphic_identity_type).
  { eapply comparison_left_conversion; [exact (type_change_comparison _ _ _ Hout)|].
    change (conv (subst a 0 (TPi E F)) (subst a 0 V)).
    apply conversion_subst; eapply cv_trans; eassumption. }
  destruct (comparison_pi_inversion _ _ _ _ Hresult) as [_ HF].
  pose proof (comparison_subst _ _ (type_change_comparison _ _ _ HCF) a 1) as HC0.
  rewrite subst_lift_prefix in HC0 by lia.
  apply (no_constant_polymorphic_identity C).
  eapply comparison_transitive; eassumption.
Qed.

Lemma identity_typing : forall Gamma A k,
  typing Gamma A (TSort k) -> typing Gamma (TLam (TVar 0)) (arrow A A).
Proof.
  intros Gamma A k HA; eapply ty_lam.
  - eapply arrow_formation; eassumption.
  - apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity].
Qed.

Lemma constant_function_typing : forall Gamma t A B k,
  typing Gamma t A -> typing Gamma B (TSort k) ->
  typing Gamma (TLam (lift 1 0 t)) (arrow B A).
Proof.
  intros Gamma t A B k Ht HB.
  destruct (type_correctness _ _ _ Ht) as [j HA].
  eapply ty_lam; [eapply arrow_formation; eassumption|].
  exact (weakening _ _ _ _ _ Ht HB).
Qed.

Lemma k_combinator_typing : forall Gamma A B j k,
  typing Gamma A (TSort j) -> typing Gamma B (TSort k) ->
  typing Gamma (TLam (TLam (TVar 1))) (arrow A (arrow B A)).
Proof.
  intros Gamma A B j k HA HB.
  eapply ty_lam; [eapply arrow_formation; [exact HA|eapply arrow_formation; eassumption]|].
  rewrite lift_arrow.
  apply (constant_function_typing _ (TVar 0) _ _ k).
  - apply smart_var; [eapply wf_cons; eauto using typing_context|reflexivity].
  - exact (weakening _ _ _ _ _ HB HA).
Qed.

Theorem polymorphic_eta_typing : typing [] polymorphic_eta polymorphic_identity_type.
Proof.
  assert (HW : wf [TSort 0]) by (eapply wf_cons; [constructor|apply ty_sort; constructor]).
  assert (HA : typing [TSort 0] (TVar 0) (TSort 0)).
  { exact (smart_var _ 0 _ HW eq_refl). }
  assert (HAA : typing [TSort 0] (arrow (TVar 0) (TVar 0)) (TSort 0)).
  { exact (arrow_formation _ _ _ 0 0 HA HA). }
  assert (HF : typing [TSort 0] monomorphic_binding
    (arrow (TSort 0) (arrow (TVar 0) (TVar 0)))).
  { unfold monomorphic_binding; eapply arrow_application.
    - eapply k_combinator_typing; [exact HAA|now apply ty_sort].
    - now apply identity_typing with (k:=0). }
  unfold polymorphic_eta, polymorphic_identity_type; eapply ty_lam with (k:=1).
  - change (typing [] (TPi (TSort 0) (arrow (TVar 0) (TVar 0))) (TSort (Nat.max 1 0))).
    apply ty_pi; [apply ty_sort; constructor|exact HAA].
  - change (typing [TSort 0] (TApp monomorphic_binding (TVar 0)) (arrow (TVar 0) (TVar 0))).
    eapply arrow_application; eassumption.
Qed.

Theorem polymorphic_eta_counterexample :
  typing [] polymorphic_eta polymorphic_identity_type /\
  reduction polymorphic_eta monomorphic_binding /\
  ~ typing [] monomorphic_binding polymorphic_identity_type.
Proof.
  split; [exact polymorphic_eta_typing|].
  split; [apply red_eta|apply monomorphic_binding_not_polymorphic].
Qed.

Print Assumptions monomorphic_binding_not_polymorphic.
Print Assumptions polymorphic_eta_counterexample.
