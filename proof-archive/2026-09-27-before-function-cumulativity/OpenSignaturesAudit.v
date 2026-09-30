(* Audit the new version without importing any legacy metatheory. *)
Require Import OpenSignatures.

Check ty_close.
Check ty_in_close.
Check ty_close_case.
Check ty_close_ind.
Check su_pi.
Check su_close.
Check es_signature.
Check ec_constructor.
Check cases_dead.

(* These seven claims must print "Closed under the global context". *)
Print Assumptions context_validity.
Print Assumptions conversion_substitution.
Print Assumptions next_step_sound.
Print Assumptions run_sound.
Print Assumptions unroll_beta.
Print Assumptions row_position_identity.
Print Assumptions singleton_source_elaborates.

(* Supporting lemmas must also have no axiom dependencies. *)
Print Assumptions fresh_id_not_in.
Print Assumptions exists_fresh_id.
Print Assumptions eval_conv.
Print Assumptions list_def_unit.
Print Assumptions nonempty_def_unit.
Print Assumptions nil_unit.

(* Checked corollaries: dependencies are listed in PROOF_STATUS.md. *)
Print Assumptions progress.
Print Assumptions preservation.
Print Assumptions confluence.
Print Assumptions consistency.
Print Assumptions normalization_eval.
Print Assumptions preservation_eval.
Print Assumptions close_induction_preservation.
Print Assumptions no_uniform_list_downcast.

(* Remaining declarations and derived typing claims are all audited. *)
Print Assumptions weakening.
Print Assumptions type_correctness.
Print Assumptions substitution.
Print Assumptions normalization.
Print Assumptions full_preservation.
Print Assumptions conversion_joinability.
Print Assumptions canonical_forms_close.
Print Assumptions canonical_forms_named.
Print Assumptions abort_typing.
Print Assumptions unroll_typing.
Print Assumptions row_code_typing.
Print Assumptions signature_typing.
Print Assumptions label_resolution_unique.
Print Assumptions dead_sound.
Print Assumptions dead_close_uninhabited.
Print Assumptions row_handlers_sound.
Print Assumptions description_subtyping_sound.
Print Assumptions subtyping_sound.
Print Assumptions case_handlers_sound.
Print Assumptions synthesis_sound.
Print Assumptions checking_sound.
Print Assumptions closing_substitution.
Print Assumptions close_roll_unroll.
Print Assumptions coercion_coherence.
Print Assumptions checking_coherence.
Print Assumptions list_definitions_well_typed.
Print Assumptions nil_typing.
Print Assumptions cons_typing.
Print Assumptions nonempty_cons_typing.
Print Assumptions reused_tree_cons_typing.
Print Assumptions nonempty_observers_typing.
Print Assumptions nonempty_widening.
Print Assumptions self_restricted_list_empty.

(* Independent binding and operational foundations. *)
Print Assumptions substitute_ext_on.
Print Assumptions substitute_identity_on.
Print Assumptions subst_fresh.
Print Assumptions substitute_alpha.
Print Assumptions free_vars_substitute.
Print Assumptions alpha_rename_lam.
Print Assumptions alpha_rename_pi.
Print Assumptions alpha_rename_sigma.
Print Assumptions substitute_compose.
Print Assumptions alpha_free_vars.
Print Assumptions typing_scoped.
Print Assumptions wf_lookup_scoped.
Print Assumptions typing_fresh_not_free.
Print Assumptions wf_type_fresh_not_free.
Print Assumptions family_formation.
Print Assumptions mu_at_formation.
Print Assumptions close_at_formation.
Print Assumptions reduction_head.
Print Assumptions alpha_head.
Print Assumptions exposes_head_reduction.
Print Assumptions step_exists_alpha.
Print Assumptions step_reduction.
Print Assumptions step_has_next.
Print Assumptions accessible_run.

(* These close over their explicit joinability premise; they introduce no
   global axioms. The public progress theorem above instantiates that premise
   with the proved conversion_joinability theorem. *)
Print Assumptions canonical_representation.
Print Assumptions bottom_no_value.
Print Assumptions progress_from_conversion.

(* Derived rules close over explicit premises and add no global axioms. *)
Print Assumptions abort_from_weakening.
Print Assumptions unroll_from_weakening.
Print Assumptions row_branches_position.
Print Assumptions row_code_from_weakening.
Print Assumptions signature_from_weakening.
Print Assumptions row_map_typing.
Print Assumptions case_term_typing.
Print Assumptions elaboration_from_rules.
Print Assumptions list_definitions_from_weakening.
Print Assumptions nonempty_widening_from_weakening.

Print Assumptions typing_domain.
Print Assumptions pi_domain_formation.
Print Assumptions alpha_same_prefix.
Print Assumptions exchange_typing.
Print Assumptions pi_coercion_typing.
Print Assumptions row_handlers_from_rules.
Print Assumptions description_subtyping_from_rules.
Print Assumptions subtyping_from_rules.

Print Assumptions raw_conversion_joinability.
Print Assumptions raw_confluence.
Print Assumptions encode_subst.
Print Assumptions encode_reduction_inverse.

Print Assumptions observers_from_weakening.

Print Assumptions typing_ctx_equal.
Print Assumptions ctx_equal_exchange.

Print Assumptions close_value_shape.
Print Assumptions typing_close_head.
Print Assumptions canonical_close_from_rules.

Print Assumptions typed_iprod_view.
Print Assumptions typed_empty_choice_view.
Print Assumptions dead_from_rules.

Print Assumptions enum_value_shape.
Print Assumptions canonical_named_from_rules.

Print Assumptions normal_endless_empty.
Print Assumptions endless_from_rules.

Print Assumptions typed_closed.
Print Assumptions subst_closed_commute.
Print Assumptions closing_from_rules.

Print Assumptions observations_separate.
Print Assumptions closed_observational_conversion.

Print Assumptions typing_encoding.
Print Assumptions typing_reflection.
Print Assumptions named_weakening.
Print Assumptions named_substitution.
Print Assumptions named_type_correctness.

Require nameless.DBBeta.
Print Assumptions nameless.DBBeta.beta_preservation.
Print Assumptions nameless.DBBeta.fst_preservation.
Print Assumptions nameless.DBBeta.snd_preservation.

Print Assumptions named_beta_preservation.
Print Assumptions named_close_payload.
