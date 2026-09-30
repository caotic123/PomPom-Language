(* Regression checks for stable bindings and capture-avoiding substitution. *)
From Stdlib Require Import List.
Require Import OpenSignaturesExamples.
Import ListNotations.

Example lookup_survives_extension :
  lookup (extend (extend empty_ctx 10 (TSort 0)) 20 (TVar 10)) 10 =
  Some (TSort 0).
Proof. reflexivity. Qed.

Example dependent_lookup_needs_no_shift :
  lookup (extend (extend empty_ctx 10 (TSort 0)) 20 (TVar 10)) 20 =
  Some (TVar 10).
Proof. reflexivity. Qed.

Example substitution_preserves_other_ids :
  subst TUnit 20 (TApp (TVar 30) (TVar 20)) = TApp (TVar 30) TUnit.
Proof. reflexivity. Qed.

Example substitution_respects_shadowing :
  subst TUnit 20 (TLam 20 (TVar 20)) = TLam 20 (TVar 20).
Proof. reflexivity. Qed.

Example substitution_avoids_capture :
  subst (TVar 30) 20 (TLam 30 (TVar 20)) = TLam 31 (TVar 30).
Proof. reflexivity. Qed.

Example substitution_renames_bound_occurrences :
  subst (TVar 30) 20 (TLam 30 (TApp (TVar 20) (TVar 30))) =
  TLam 31 (TApp (TVar 30) (TVar 31)).
Proof. reflexivity. Qed.

Example binder_does_not_scope_over_its_domain :
  subst TUnit 10 (TPi 10 (TVar 10) (TVar 10)) =
  TPi 10 TUnit (TVar 10).
Proof. reflexivity. Qed.

Example context_extension_keeps_dependent_types :
  lookup (extend (extend (extend empty_ctx 10 (TSort 0))
    20 (TVar 10)) 30 TUnitT) 20 = Some (TVar 10).
Proof. reflexivity. Qed.

Example alpha_identity :
  alpha_eqb (TLam 10 (TVar 10)) (TLam 20 (TVar 20)) = true.
Proof. reflexivity. Qed.

Example alpha_keeps_free_ids_distinct :
  alpha_eqb (TLam 10 (TVar 30)) (TLam 20 (TVar 40)) = false.
Proof. reflexivity. Qed.

Example alpha_distinguishes_free_from_bound :
  alpha_eqb (TLam 10 (TVar 20)) (TLam 20 (TVar 20)) = false.
Proof. reflexivity. Qed.

Example alpha_respects_shadowing :
  alpha_eqb (TLam 10 (TLam 10 (TVar 10)))
    (TLam 20 (TLam 30 (TVar 30))) = true.
Proof. reflexivity. Qed.

Example alpha_distinguishes_inner_and_outer_binders :
  alpha_eqb (TLam 10 (TLam 20 (TVar 10)))
    (TLam 30 (TLam 30 (TVar 30))) = false.
Proof. reflexivity. Qed.

Example alpha_pi_domain_is_outside_binder :
  alpha_eqb (TPi 10 (TVar 10) (TVar 10))
    (TPi 20 (TVar 10) (TVar 20)) = true.
Proof. reflexivity. Qed.

Example alpha_compares_open_terms_under_two_contexts :
  alpha_eqb_in [10] [20]
    (TApp (TVar 10) (TVar 99)) (TApp (TVar 20) (TVar 99)) = true.
Proof. reflexivity. Qed.

Example alpha_contexts_keep_bound_and_free_ids_distinct :
  alpha_eqb_in [10] [20] (TVar 10) (TVar 10) = false.
Proof. reflexivity. Qed.

Example alpha_contexts_respect_inner_shadowing :
  alpha_eqb_in [10] [20]
    (TLam 10 (TVar 10)) (TLam 30 (TVar 20)) = false.
Proof. reflexivity. Qed.

Example alpha_preserves_universe_levels :
  alpha_eqb (TSort 0) (TSort 1) = false.
Proof. reflexivity. Qed.

Example alpha_is_not_beta_conversion :
  alpha_eqb (TApp (TLam 10 (TVar 10)) TUnit) TUnit = false.
Proof. reflexivity. Qed.

Example beta_uses_the_recorded_id :
  root_step (TApp (TLam 20 (TVar 20)) TUnit) = Some TUnit.
Proof. reflexivity. Qed.

Example beta_keeps_an_unrelated_id :
  root_step (TApp (TLam 20 (TVar 99)) TUnit) = Some (TVar 99).
Proof. reflexivity. Qed.

Example beta_avoids_capture :
  root_step (TApp (TLam 20 (TLam 30 (TVar 20))) (TVar 30)) =
  Some (TLam 31 (TVar 30)).
Proof. reflexivity. Qed.

Lemma test_type_binding_wf : wf (extend empty_ctx 10 (TSort 0)).
Proof.
  eapply wf_cons with (k := 1).
  - apply wf_nil.
  - apply ty_sort, wf_nil.
  - reflexivity.
Qed.

Lemma test_dependent_context_wf :
  wf (extend (extend empty_ctx 10 (TSort 0)) 20 (TVar 10)).
Proof.
  eapply wf_cons with (k := 0).
  - apply test_type_binding_wf.
  - apply ty_var; [apply test_type_binding_wf | reflexivity].
  - reflexivity.
Qed.

Example variable_type_uses_its_stable_id :
  typing (extend (extend empty_ctx 10 (TSort 0)) 20 (TVar 10))
    (TVar 20) (TVar 10).
Proof. apply ty_var; [apply test_dependent_context_wf | reflexivity]. Qed.

Example interning_starts_at_zero :
  intern empty_arena (TLam 10 (TVar 10)) = ([TLam 10 (TVar 10)], 0).
Proof. reflexivity. Qed.

Example interning_reuses_an_alpha_class :
  let '(a, first) := intern empty_arena (TLam 10 (TVar 10)) in
  intern a (TLam 20 (TVar 20)) = (a, first).
Proof. reflexivity. Qed.

Example interning_allocates_sequential_ids :
  let '(a, first) := intern empty_arena (TLam 10 (TVar 10)) in
  intern a TUnit = ([TLam 10 (TVar 10); TUnit], S first).
Proof. reflexivity. Qed.

Example interning_preserves_existing_references :
  let '(a, first) := intern empty_arena (TLam 10 (TVar 10)) in
  let '(a', _) := intern a TUnit in
  resolve a' first = Some (TLam 10 (TVar 10)).
Proof. reflexivity. Qed.

Example interning_distinguishes_free_ids :
  let '(a, _) := intern empty_arena (TVar 10) in
  intern a (TVar 20) = ([TVar 10; TVar 20], 1).
Proof. reflexivity. Qed.

Example alpha_renaming_preserves_typing :
  typing empty_ctx (TLam 20 (TVar 20)) (TPi 10 TUnitT TUnitT).
Proof.
  assert (Hwf : wf (extend empty_ctx 10 TUnitT)).
  { apply wf_cons with (k := 0).
    - apply wf_nil.
    - apply ty_unitT, wf_nil.
    - reflexivity. }
  eapply ty_alpha with (t := TLam 10 (TVar 10)).
  - apply ty_lam with (k := 0).
    + reflexivity.
    + apply ty_pi with (j := 0) (k := 0).
      * reflexivity.
      * apply ty_unitT, wf_nil.
      * apply ty_unitT, Hwf.
    + apply ty_var; [exact Hwf | reflexivity].
  - apply alpha_lam_identity.
Qed.
