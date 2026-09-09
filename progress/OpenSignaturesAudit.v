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

(* These are intentionally unproved and must print as assumptions. *)
Print Assumptions progress.
Print Assumptions preservation.
Print Assumptions normalization.
Print Assumptions confluence.
Print Assumptions consistency.
Print Assumptions dead_sound.
Print Assumptions subtyping_sound.
Print Assumptions synthesis_sound.
Print Assumptions checking_sound.
Print Assumptions coercion_coherence.
Print Assumptions checking_coherence.
Print Assumptions nonempty_widening.

(* These closed computations must not depend on any conjecture. *)
Print Assumptions head_singleton_computes.
Print Assumptions tail_singleton_computes.
Print Assumptions widening_changes_local_tag.
Print Assumptions widening_keeps_the_list_tail.
Print Assumptions compact_padded_roundtrip.
Print Assumptions bottom_interpretation_computes.
Print Assumptions close_types_do_not_unfold.
Print Assumptions signature_application_keeps_its_type_parameter.
Print Assumptions dependent_codomain_keeps_outer_variables.
Print Assumptions pi_coercion_inserts_function_below_argument.
