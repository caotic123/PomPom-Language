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

Print Assumptions checked_annotated_foundations.
Print Assumptions checked_annotated_preservation.
