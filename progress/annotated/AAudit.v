(* One shared dependency audit for the annotated repair. *)
Require annotated.ARegression.

Definition checked_annotated_foundations :=
  (@annotated.AErasure.erase_lift,
   @annotated.AErasure.erase_subst,
   @annotated.AFreshness.occurs_false_iff_lift,
   @annotated.AEta.eta_contract_sound,
   @annotated.AEta.eta_contract_complete,
   @annotated.AEta.eta_root_lift,
   @annotated.AEta.eta_root_subst,
   @annotated.AEta.structural_step_conversion,
   @annotated.ATyping.typing_erasure,
   @annotated.ATyping.typing_context,
   @annotated.ATyping.type_correctness,
   @annotated.AWeakening.typing_lift,
   @annotated.ASubstitution.typing_subst,
   @annotated.ASubstitution.substitution,
   @annotated.AComparison.comparison_typing,
   @annotated.AGeneration.lambda_generation,
   @annotated.AGeneration.application_generation,
   @annotated.ABeta.beta_preservation,
   @annotated.ARegression.annotated_source_typing,
   @annotated.ARegression.bad_eta_has_no_root,
   @annotated.ARegression.general_eta_allowed,
   @annotated.ARegression.annotation_erasure_is_not_eta_freshness).

Require annotated.AStructuralPreservation.

Definition checked_annotated_preservation :=
  (@annotated.AStructuralPreservation.structural_root_preservation,
   @annotated.AStructuralPreservation.structural_step_preservation).

Require annotated.AFullPreservation.

Definition checked_annotated_full_preservation :=
  (@annotated.AFullPreservation.full_preservation,
   @annotated.AFullPreservation.full_preservation_reduces,
   @annotated.AFullPreservation.reduction_erasure,
   @annotated.AFullPreservation.reduces_erasure).

Require annotated.ACriticalPair.

Definition checked_annotated_critical_pair :=
  (@annotated.ACriticalPair.widened_redex_typing,
   @annotated.ACriticalPair.reducts_same_erasure,
   @annotated.ACriticalPair.annotated_reduction_not_confluent).

Require annotated.ACompleteness annotated.ACfConfluence.

Definition checked_annotated_bridges :=
  (@annotated.ACompleteness.annotation_completeness,
   @annotated.ACompleteness.typing_iff_annotation,
   @annotated.AStepFunction.aroot_step_sound,
   @annotated.AStepFunction.aroot_step_complete,
   @annotated.AStepFunction.reduction_decidable,
   @annotated.ACfNormal.typed_normal_erasure,
   @annotated.ACfConfluence.normal_forms_unique_modulo_annotations,
   @annotated.ACfConfluence.confluence_modulo_annotations,
   @annotated.ACfConfluence.conversion_joinability_modulo_annotations).

Print Assumptions checked_annotated_foundations.
Print Assumptions checked_annotated_preservation.
Print Assumptions checked_annotated_full_preservation.
Print Assumptions checked_annotated_critical_pair.
Print Assumptions checked_annotated_bridges.
