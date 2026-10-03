(* Bind each proof at its original point of name resolution, then traverse
   the shared dependency graph once. This avoids repeatedly scanning the
   normalization proof and preserves coverage despite later module imports.
   The two coherence theorems are also printed separately. *)
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

(* These seven claims are included in the closed bundle below. *)
Local Definition audited_closed_001 := @context_validity.
Local Definition audited_closed_002 := @conversion_substitution.
Local Definition audited_closed_003 := @next_step_sound.
Local Definition audited_closed_004 := @run_sound.
Local Definition audited_closed_005 := @unroll_beta.
Local Definition audited_closed_006 := @row_position_identity.
Local Definition audited_closed_007 := @singleton_source_elaborates.

(* Supporting lemmas must also have no axiom dependencies. *)
Local Definition audited_closed_008 := @fresh_id_not_in.
Local Definition audited_closed_009 := @exists_fresh_id.
Local Definition audited_closed_010 := @eval_conv.
Local Definition audited_closed_011 := @list_def_unit.
Local Definition audited_closed_012 := @nonempty_def_unit.
Local Definition audited_closed_013 := @nil_unit.

(* Checked corollaries: dependencies are listed in PROOF_STATUS.md. *)
Local Definition audited_closed_014 := @progress.
Local Definition audited_closed_015 := @preservation.
Local Definition audited_closed_016 := @confluence.
Local Definition audited_closed_017 := @consistency.
Local Definition audited_closed_018 := @normalization_eval.
Local Definition audited_closed_019 := @preservation_eval.
Local Definition audited_closed_020 := @close_induction_preservation.
Local Definition audited_closed_021 := @no_uniform_list_downcast.

(* Remaining declarations and derived typing claims are all audited. *)
Local Definition audited_closed_022 := @weakening.
Local Definition audited_closed_023 := @type_correctness.
Local Definition audited_closed_024 := @substitution.
Local Definition audited_closed_025 := @normalization.
(* The original full-preservation proposition is false, not an open axiom. *)
Check full_preservation_statement.
Local Definition audited_closed_026 := @full_preservation_refuted.
Local Definition audited_closed_027 := @unrestricted_eta_counterexample.
Local Definition audited_closed_028 := @conversion_joinability.
Local Definition audited_closed_029 := @canonical_forms_close.
Local Definition audited_closed_030 := @canonical_forms_named.
Local Definition audited_closed_031 := @abort_typing.
Local Definition audited_closed_032 := @unroll_typing.
Local Definition audited_closed_033 := @row_code_typing.
Local Definition audited_closed_034 := @signature_typing.
Local Definition audited_closed_035 := @label_resolution_unique.
Local Definition audited_closed_036 := @dead_sound.
Local Definition audited_closed_037 := @dead_close_uninhabited.
Local Definition audited_closed_038 := @row_handlers_sound.
Local Definition audited_closed_039 := @description_subtyping_sound.
Local Definition audited_closed_040 := @subtyping_sound.
Local Definition audited_closed_041 := @case_handlers_sound.
Local Definition audited_closed_042 := @synthesis_sound.
Local Definition audited_closed_043 := @checking_sound.
Local Definition audited_closed_044 := @closing_substitution.
Local Definition audited_closed_045 := @close_roll_unroll.
Print Assumptions coercion_coherence.
Print Assumptions checking_coherence.
Local Definition audited_closed_046 := @list_definitions_well_typed.
Local Definition audited_closed_047 := @nil_typing.
Local Definition audited_closed_048 := @cons_typing.
Local Definition audited_closed_049 := @nonempty_cons_typing.
Local Definition audited_closed_050 := @reused_tree_cons_typing.
Local Definition audited_closed_051 := @nonempty_observers_typing.
Local Definition audited_closed_052 := @nonempty_widening.
Local Definition audited_closed_053 := @self_restricted_list_empty.

(* Independent binding and operational foundations. *)
Local Definition audited_closed_054 := @substitute_ext_on.
Local Definition audited_closed_055 := @substitute_identity_on.
Local Definition audited_closed_056 := @subst_fresh.
Local Definition audited_closed_057 := @substitute_alpha.
Local Definition audited_closed_058 := @free_vars_substitute.
Local Definition audited_closed_059 := @alpha_rename_lam.
Local Definition audited_closed_060 := @alpha_rename_pi.
Local Definition audited_closed_061 := @alpha_rename_sigma.
Local Definition audited_closed_062 := @substitute_compose.
Local Definition audited_closed_063 := @alpha_free_vars.
Local Definition audited_closed_064 := @typing_scoped.
Local Definition audited_closed_065 := @wf_lookup_scoped.
Local Definition audited_closed_066 := @typing_fresh_not_free.
Local Definition audited_closed_067 := @wf_type_fresh_not_free.
Local Definition audited_closed_068 := @family_formation.
Local Definition audited_closed_069 := @mu_at_formation.
Local Definition audited_closed_070 := @close_at_formation.
Local Definition audited_closed_071 := @reduction_head.
Local Definition audited_closed_072 := @alpha_head.
Local Definition audited_closed_073 := @exposes_head_reduction.
Local Definition audited_closed_074 := @step_exists_alpha.
Local Definition audited_closed_075 := @step_reduction.
Local Definition audited_closed_076 := @step_has_next.
Local Definition audited_closed_077 := @accessible_run.

(* These close over their explicit joinability premise; they introduce no
   global axioms. The public progress theorem above instantiates that premise
   with the proved conversion_joinability theorem. *)
Local Definition audited_closed_078 := @canonical_representation.
Local Definition audited_closed_079 := @bottom_no_value.
Local Definition audited_closed_080 := @progress_from_conversion.

(* Derived rules close over explicit premises and add no global axioms. *)
Local Definition audited_closed_081 := @abort_from_weakening.
Local Definition audited_closed_082 := @unroll_from_weakening.
Local Definition audited_closed_083 := @row_branches_position.
Local Definition audited_closed_084 := @row_code_from_weakening.
Local Definition audited_closed_085 := @signature_from_weakening.
Local Definition audited_closed_086 := @row_map_typing.
Local Definition audited_closed_087 := @case_term_typing.
Local Definition audited_closed_088 := @elaboration_from_rules.
Local Definition audited_closed_089 := @list_definitions_from_weakening.
Local Definition audited_closed_090 := @nonempty_widening_from_weakening.

Local Definition audited_closed_091 := @typing_domain.
Local Definition audited_closed_092 := @pi_domain_formation.
Local Definition audited_closed_093 := @alpha_same_prefix.
Local Definition audited_closed_094 := @exchange_typing.
Local Definition audited_closed_095 := @pi_coercion_typing.
Local Definition audited_closed_096 := @row_handlers_from_rules.
Local Definition audited_closed_097 := @description_subtyping_from_rules.
Local Definition audited_closed_098 := @subtyping_from_rules.

Local Definition audited_closed_099 := @raw_conversion_joinability.
Local Definition audited_closed_100 := @raw_confluence.
Local Definition audited_closed_101 := @encode_subst.
Local Definition audited_closed_102 := @encode_reduction_inverse.

Local Definition audited_closed_103 := @observers_from_weakening.

Local Definition audited_closed_104 := @typing_ctx_equal.
Local Definition audited_closed_105 := @ctx_equal_exchange.

Local Definition audited_closed_106 := @close_value_shape.
Local Definition audited_closed_107 := @typing_close_head.
Local Definition audited_closed_108 := @canonical_close_from_rules.

Local Definition audited_closed_109 := @typed_iprod_view.
Local Definition audited_closed_110 := @typed_empty_choice_view.
Local Definition audited_closed_111 := @dead_from_rules.

Local Definition audited_closed_112 := @enum_value_shape.
Local Definition audited_closed_113 := @canonical_named_from_rules.

Local Definition audited_closed_114 := @normal_endless_empty.
Local Definition audited_closed_115 := @endless_from_rules.

Local Definition audited_closed_116 := @typed_closed.
Local Definition audited_closed_117 := @subst_closed_commute.
Local Definition audited_closed_118 := @closing_from_rules.

Local Definition audited_closed_119 := @observations_separate.
Local Definition audited_closed_120 := @closed_observational_conversion.

Local Definition audited_closed_121 := @typing_encoding.
Local Definition audited_closed_122 := @typing_reflection.
Local Definition audited_closed_123 := @named_weakening.
Local Definition audited_closed_124 := @named_substitution.
Local Definition audited_closed_125 := @named_type_correctness.

Require nameless.DBBeta.
Local Definition audited_closed_126 := @nameless.DBBeta.beta_preservation.
Local Definition audited_closed_127 := @nameless.DBBeta.fst_preservation.
Local Definition audited_closed_128 := @nameless.DBBeta.snd_preservation.

Local Definition audited_closed_129 := @named_beta_preservation.
Local Definition audited_closed_130 := @named_close_payload.

Print universe_le.
Check ty_cumul_fun.
Local Definition audited_closed_131 := @nameless.DBContexts.context_narrowing.

(* Computation, postponement, and normalization foundations. *)
Require nameless.DBNormalization.
Local Definition audited_closed_132 := @nameless.DBComputationPreservation.computation_preservation.
Local Definition audited_closed_133 := @nameless.DBParallelPreservation.pstep_preservation.
Local Definition audited_closed_134 := @nameless.DBEtaSafety.typing_eta_safe.
Local Definition audited_closed_135 := @nameless.DBEtaSafety.epstep_eta_safe.
Local Definition audited_closed_136 := @nameless.DBEtaPostponement.safe_eta_pstep_postpone.
Local Definition audited_closed_137 := @nameless.DBEtaPostponement.typed_reduction_factorization.
Local Definition audited_closed_138 := @nameless.DBDescriptionViews.typed_iprod_view.
Local Definition audited_closed_139 := @nameless.DBDescriptionViews.typed_empty_choice_view.
Local Definition audited_closed_140 := @nameless.DBNormalization.eta_normalization.
Local Definition audited_closed_141 := @nameless.DBNormalization.normalization_from_phases.

(* Computational activity, eta transfer, and reducibility: all axiom-free. *)
Require Import nameless.DBReducibility.
Local Definition audited_closed_142 := @nameless.DBActiveParallel.apstep_positive.
Local Definition audited_closed_143 := @nameless.DBActivePostponement.safe_eta_apstep_postpone.
Local Definition audited_closed_144 := @nameless.DBActivePostponement.safe_etas_apstep_postpone.
Local Definition audited_closed_145 := @nameless.DBNormalization.normalization_from_computation.
Local Definition audited_closed_146 := @named_normalization_from_computation.
Local Definition audited_closed_147 := @nameless.DBComputationSubstitution.computation_subst.
Local Definition audited_closed_148 := @nameless.DBComputationSubstitution.substitution_reflects_normalization.
Local Definition audited_closed_149 := @nameless.DBReducibility.dependent_function_candidate.
Local Definition audited_closed_150 := @nameless.DBReducibility.dependent_lambda_computable.
Local Definition audited_closed_151 := @nameless.DBReducibility.dependent_pair_candidate.
Local Definition audited_closed_152 := @nameless.DBReducibility.dependent_pair_computable.
Local Definition audited_closed_153 := @nameless.DBReducibility.dependent_function_eta.
Local Definition audited_closed_154 := @nameless.DBReducibility.dependent_function_variance.

(* Full reduction, semantic universes, and positive candidate fixed points. *)
Require Import nameless.DBSemanticTypes nameless.DBUniverseModel nameless.DBPositiveCandidates.
Local Definition audited_closed_155 := @nameless.DBFullReductionStructure.reduction_lift.
Local Definition audited_closed_156 := @nameless.DBFullReductionStructure.reduction_subst.
Local Definition audited_closed_157 := @nameless.DBFullNormalForms.full_next_complete.
Local Definition audited_closed_158 := @nameless.DBFullNormalForms.normalize_full.
Local Definition audited_closed_159 := @nameless.DBFullReducibility.Full.dependent_lambda_computable.
Local Definition audited_closed_160 := @nameless.DBFullReducibility.Full.dependent_pair_computable.
Local Definition audited_closed_161 := @nameless.DBSemanticTypes.type_interp_unique.
Local Definition audited_closed_162 := @nameless.DBSemanticTypes.type_interp_canonical.
Local Definition audited_closed_163 := @nameless.DBSemanticTypes.reducible_type_candidate.
Local Definition audited_closed_164 := @nameless.DBUniverseModel.universe_model_candidate.
Local Definition audited_closed_165 := @nameless.DBUniverseModel.universe_model_cumulative.
Local Definition audited_closed_166 := @nameless.DBUniverseModel.universe_interp_unique.
Local Definition audited_closed_167 := @nameless.DBUniverseModel.universe_pi_formation.
Local Definition audited_closed_168 := @nameless.DBUniverseModel.universe_sigma_formation.
Local Definition audited_closed_169 := @nameless.DBPositiveCandidates.positive_mu_candidate.
Local Definition audited_closed_170 := @nameless.DBPositiveCandidates.positive_mu_fold.
Local Definition audited_closed_171 := @nameless.DBPositiveCandidates.positive_mu_unfold.

(* Concrete description and small-type semantics. *)
Require Import nameless.DBSemanticGeneration.
Local Definition audited_closed_172 := @nameless.DBIndexedCandidates.Indexed.mu_candidate.
Local Definition audited_closed_173 := @nameless.DBIndexedCandidates.Indexed.mu_unfold.
Local Definition audited_closed_174 := @nameless.DBIndexedCandidates.Indexed.mu_refinement.
Local Definition audited_closed_175 := @nameless.DBIndexedCandidates.Indexed.mu_model_equiv.
Local Definition audited_closed_176 := @nameless.DBDescriptionCandidates.description_computable_candidate.
Local Definition audited_closed_177 := @nameless.DBEnumCandidates.enum_elements_candidate.
Local Definition audited_closed_178 := @nameless.DBEnumCandidates.enum_elements_conversion.
Local Definition audited_closed_179 := @nameless.DBEnumCandidates.enum_elements_empty.
Local Definition audited_closed_180 := @nameless.DBDescriptionModel.description_interp_unique.
Local Definition audited_closed_181 := @nameless.DBDescriptionModel.description_interp_candidate.
Local Definition audited_closed_182 := @nameless.DBDescriptionModel.description_interp_monotone.
Local Definition audited_closed_183 := @nameless.DBDescriptionModel.computable_description_interpreted.
Local Definition audited_closed_184 := @nameless.DBSmallTypeModel.small_atom_unique.
Local Definition audited_closed_185 := @nameless.DBSmallTypeModel.small_mu_atom.
Local Definition audited_closed_186 := @nameless.DBSmallTypeModel.small_close_atom.
Local Definition audited_closed_187 := @nameless.DBCalculusModel.calculus_interp_unique.
Local Definition audited_closed_188 := @nameless.DBCalculusModel.calculus_pi_formation.
Local Definition audited_closed_189 := @nameless.DBCalculusModel.calculus_description_formation.
Local Definition audited_closed_190 := @nameless.DBCalculusModel.calculus_mu_type.
Local Definition audited_closed_191 := @nameless.DBCalculusModel.calculus_close_type.
Local Definition audited_closed_192 := @nameless.DBSemanticGeneration.type_interp_pi_view.
Local Definition audited_closed_193 := @nameless.DBSemanticGeneration.calculus_sort_view.

(* Full-reduction computability of every primitive semantic operator.
   The full fundamental theorem below connects every typing rule to this model. *)
Require Import nameless.DBCloseIndComputability.
Local Definition audited_closed_194 := @nameless.DBHeadExpansion.computability_by_head_expansion.
Local Definition audited_closed_195 := @nameless.DBInterpretationComputability.interpretation_computable.
Local Definition audited_closed_196 := @nameless.DBAllComputability.all_computable.
Local Definition audited_closed_197 := @nameless.DBHypsComputability.hyps_computable.
Local Definition audited_closed_198 := @nameless.DBSaturatedElimination.saturated_elimination.
Local Definition audited_closed_199 := @nameless.DBCloseCaseComputability.close_case_computable.
Local Definition audited_closed_200 := @nameless.DBEnumCandidates.enumeration_computable_candidate.
Local Definition audited_closed_201 := @nameless.DBEnumComputability.epi_computable.
Local Definition audited_closed_202 := @nameless.DBSwitchComputability.switch_computable.
Local Definition audited_closed_203 := @nameless.DBEliminatorCandidates.eliminator_refinement_candidate.
Local Definition audited_closed_204 := @nameless.DBBetaExpansion.candidate_beta_expansion.
Local Definition audited_closed_205 := @nameless.DBBetaExpansion.dependent_double_lambda_computable.
Local Definition audited_closed_206 := @nameless.DBIndComputability.ind_computable.
Local Definition audited_closed_207 := @nameless.DBDataComputability.small_fixed_point_rolled_equiv.
Local Definition audited_closed_208 := @nameless.DBCloseIndComputability.close_ind_computable.

Require Import nameless.DBSemanticJudgments.
Local Definition audited_closed_209 := @nameless.DBSemanticBinders.calculus_pi_components.
Local Definition audited_closed_210 := @nameless.DBSemanticBinders.calculus_sigma_components.
Local Definition audited_closed_211 := @nameless.DBSemanticJudgments.semantic_lambda.
Local Definition audited_closed_212 := @nameless.DBSemanticJudgments.semantic_application.
Local Definition audited_closed_213 := @nameless.DBSemanticJudgments.semantic_pair.
Local Definition audited_closed_214 := @nameless.DBSemanticJudgments.semantic_cumulative.

Require Import nameless.DBSemanticVariance.
Local Definition audited_closed_215 := @nameless.DBSemanticVariance.universe_le_semantics.
Local Definition audited_closed_216 := @nameless.DBSemanticVariance.semantic_function_cumulative.

Require Import nameless.DBSemanticSubstitution.
Local Definition audited_closed_217 := @nameless.DBSemanticSubstitution.instantiate_extension.
Local Definition audited_closed_218 := @nameless.DBSemanticSubstitution.instantiate_subst.
Local Definition audited_closed_219 := @nameless.DBSemanticSubstitution.reduction_instantiate.
Local Definition audited_closed_220 := @nameless.DBSemanticSubstitution.instantiation_reflects_normalization.
Local Definition audited_closed_221 := @nameless.DBSemanticSubstitution.semantic_environment_extend.

(* Full fundamental theorem and named normalization: no conjecture premises. *)
Require Import nameless.DBSemanticFundamental.
Local Definition audited_closed_222 := @nameless.DBSemanticFundamental.semantic_fundamental.
Local Definition audited_closed_223 := @nameless.DBSemanticFundamental.semantic_environment_inhabited.
Local Definition audited_closed_224 := @nameless.DBSemanticFundamental.typing_full_normalization.
Local Definition audited_closed_225 := @OpenSignaturesNormalization.named_full_normalization.

(* Typed comparison chains and eta contraction at stable principal types. *)
Require nameless.DBEtaPrincipal.
Local Definition audited_closed_226 := @nameless.DBCumulativeTyping.type_change_pi.
Local Definition audited_closed_227 := @nameless.DBTypedPiViews.typed_pi_view.
Local Definition audited_closed_228 := @nameless.DBTypeComparison.comparison_transitive.
Local Definition audited_closed_229 := @nameless.DBTypeComparison.comparison_realization.
Local Definition audited_closed_230 := @nameless.DBTypeComparison.type_change_strengthening.
Local Definition audited_closed_231 := @nameless.DBEtaPrincipal.eta_principal_preservation.
Local Definition audited_closed_232 := @nameless.DBEtaPrincipal.eta_variable_preservation.

(* Closed contextual-equivalence infrastructure for the remaining coherence proofs. *)
Require OpenSignaturesObservationalLaws.
Local Definition audited_closed_233 := @OpenSignaturesObservations.named_closing_substitution.
Local Definition audited_closed_234 := @OpenSignaturesObservations.observational_conversion.
Local Definition audited_closed_235 := @OpenSignaturesObservationalLaws.closed_observational_function_tests.
Local Definition audited_closed_236 := @OpenSignaturesObservationalLaws.closed_observational_congruence.
Local Definition audited_closed_237 := @OpenSignaturesObservationalLaws.closed_observational_context.

Require OpenSignaturesObservationalTypes.
Local Definition audited_closed_238 := @OpenSignaturesObservationalTypes.closed_observational_type_conversion.
Local Definition audited_closed_239 := @OpenSignaturesObservationalTypes.observational_type_conversion.
Local Definition audited_closed_240 := @OpenSignaturesObservationalTypes.closed_observational_application.

(* Full compatible computation is a checked replacement option; it does not
   discharge the refuted beta/eta preservation proposition. *)
Require OpenSignaturesComputationPreservation.
Local Definition audited_closed_241 := @OpenSignaturesComputationPreservation.named_computation_preservation.

(* Closed live-row behavior, independent of either coherence conjecture. *)
Require OpenSignaturesRowCoherence.
Local Definition audited_closed_242 := @OpenSignaturesRowCoherence.row_handlers_live_at.
Local Definition audited_closed_243 := @OpenSignaturesRowCoherence.row_payload_canonical.
Local Definition audited_closed_244 := @OpenSignaturesRowCoherence.row_maps_closed_pointwise_coherence.

Require OpenSignaturesRowViews OpenSignaturesDescriptionCoherence.
Local Definition audited_closed_245 := @OpenSignaturesRowViews.row_view_position_transport.
Local Definition audited_closed_246 := @OpenSignaturesDescriptionCoherence.description_conversion_identity.
Local Definition audited_closed_247 := @OpenSignaturesDescriptionCoherence.description_coercions_closed_pointwise_coherence.

Local Definition audited_closed_proofs :=
  (@audited_closed_001,
   @audited_closed_002,
   @audited_closed_003,
   @audited_closed_004,
   @audited_closed_005,
   @audited_closed_006,
   @audited_closed_007,
   @audited_closed_008,
   @audited_closed_009,
   @audited_closed_010,
   @audited_closed_011,
   @audited_closed_012,
   @audited_closed_013,
   @audited_closed_014,
   @audited_closed_015,
   @audited_closed_016,
   @audited_closed_017,
   @audited_closed_018,
   @audited_closed_019,
   @audited_closed_020,
   @audited_closed_021,
   @audited_closed_022,
   @audited_closed_023,
   @audited_closed_024,
   @audited_closed_025,
   @audited_closed_026,
   @audited_closed_027,
   @audited_closed_028,
   @audited_closed_029,
   @audited_closed_030,
   @audited_closed_031,
   @audited_closed_032,
   @audited_closed_033,
   @audited_closed_034,
   @audited_closed_035,
   @audited_closed_036,
   @audited_closed_037,
   @audited_closed_038,
   @audited_closed_039,
   @audited_closed_040,
   @audited_closed_041,
   @audited_closed_042,
   @audited_closed_043,
   @audited_closed_044,
   @audited_closed_045,
   @audited_closed_046,
   @audited_closed_047,
   @audited_closed_048,
   @audited_closed_049,
   @audited_closed_050,
   @audited_closed_051,
   @audited_closed_052,
   @audited_closed_053,
   @audited_closed_054,
   @audited_closed_055,
   @audited_closed_056,
   @audited_closed_057,
   @audited_closed_058,
   @audited_closed_059,
   @audited_closed_060,
   @audited_closed_061,
   @audited_closed_062,
   @audited_closed_063,
   @audited_closed_064,
   @audited_closed_065,
   @audited_closed_066,
   @audited_closed_067,
   @audited_closed_068,
   @audited_closed_069,
   @audited_closed_070,
   @audited_closed_071,
   @audited_closed_072,
   @audited_closed_073,
   @audited_closed_074,
   @audited_closed_075,
   @audited_closed_076,
   @audited_closed_077,
   @audited_closed_078,
   @audited_closed_079,
   @audited_closed_080,
   @audited_closed_081,
   @audited_closed_082,
   @audited_closed_083,
   @audited_closed_084,
   @audited_closed_085,
   @audited_closed_086,
   @audited_closed_087,
   @audited_closed_088,
   @audited_closed_089,
   @audited_closed_090,
   @audited_closed_091,
   @audited_closed_092,
   @audited_closed_093,
   @audited_closed_094,
   @audited_closed_095,
   @audited_closed_096,
   @audited_closed_097,
   @audited_closed_098,
   @audited_closed_099,
   @audited_closed_100,
   @audited_closed_101,
   @audited_closed_102,
   @audited_closed_103,
   @audited_closed_104,
   @audited_closed_105,
   @audited_closed_106,
   @audited_closed_107,
   @audited_closed_108,
   @audited_closed_109,
   @audited_closed_110,
   @audited_closed_111,
   @audited_closed_112,
   @audited_closed_113,
   @audited_closed_114,
   @audited_closed_115,
   @audited_closed_116,
   @audited_closed_117,
   @audited_closed_118,
   @audited_closed_119,
   @audited_closed_120,
   @audited_closed_121,
   @audited_closed_122,
   @audited_closed_123,
   @audited_closed_124,
   @audited_closed_125,
   @audited_closed_126,
   @audited_closed_127,
   @audited_closed_128,
   @audited_closed_129,
   @audited_closed_130,
   @audited_closed_131,
   @audited_closed_132,
   @audited_closed_133,
   @audited_closed_134,
   @audited_closed_135,
   @audited_closed_136,
   @audited_closed_137,
   @audited_closed_138,
   @audited_closed_139,
   @audited_closed_140,
   @audited_closed_141,
   @audited_closed_142,
   @audited_closed_143,
   @audited_closed_144,
   @audited_closed_145,
   @audited_closed_146,
   @audited_closed_147,
   @audited_closed_148,
   @audited_closed_149,
   @audited_closed_150,
   @audited_closed_151,
   @audited_closed_152,
   @audited_closed_153,
   @audited_closed_154,
   @audited_closed_155,
   @audited_closed_156,
   @audited_closed_157,
   @audited_closed_158,
   @audited_closed_159,
   @audited_closed_160,
   @audited_closed_161,
   @audited_closed_162,
   @audited_closed_163,
   @audited_closed_164,
   @audited_closed_165,
   @audited_closed_166,
   @audited_closed_167,
   @audited_closed_168,
   @audited_closed_169,
   @audited_closed_170,
   @audited_closed_171,
   @audited_closed_172,
   @audited_closed_173,
   @audited_closed_174,
   @audited_closed_175,
   @audited_closed_176,
   @audited_closed_177,
   @audited_closed_178,
   @audited_closed_179,
   @audited_closed_180,
   @audited_closed_181,
   @audited_closed_182,
   @audited_closed_183,
   @audited_closed_184,
   @audited_closed_185,
   @audited_closed_186,
   @audited_closed_187,
   @audited_closed_188,
   @audited_closed_189,
   @audited_closed_190,
   @audited_closed_191,
   @audited_closed_192,
   @audited_closed_193,
   @audited_closed_194,
   @audited_closed_195,
   @audited_closed_196,
   @audited_closed_197,
   @audited_closed_198,
   @audited_closed_199,
   @audited_closed_200,
   @audited_closed_201,
   @audited_closed_202,
   @audited_closed_203,
   @audited_closed_204,
   @audited_closed_205,
   @audited_closed_206,
   @audited_closed_207,
   @audited_closed_208,
   @audited_closed_209,
   @audited_closed_210,
   @audited_closed_211,
   @audited_closed_212,
   @audited_closed_213,
   @audited_closed_214,
   @audited_closed_215,
   @audited_closed_216,
   @audited_closed_217,
   @audited_closed_218,
   @audited_closed_219,
   @audited_closed_220,
   @audited_closed_221,
   @audited_closed_222,
   @audited_closed_223,
   @audited_closed_224,
   @audited_closed_225,
   @audited_closed_226,
   @audited_closed_227,
   @audited_closed_228,
   @audited_closed_229,
   @audited_closed_230,
   @audited_closed_231,
   @audited_closed_232,
   @audited_closed_233,
   @audited_closed_234,
   @audited_closed_235,
   @audited_closed_236,
   @audited_closed_237,
   @audited_closed_238,
   @audited_closed_239,
   @audited_closed_240,
   @audited_closed_241,
   @audited_closed_242,
   @audited_closed_243,
   @audited_closed_244,
   @audited_closed_245,
   @audited_closed_246,
   @audited_closed_247).

Print Assumptions audited_closed_proofs.
