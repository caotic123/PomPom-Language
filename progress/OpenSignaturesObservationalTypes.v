(* Conversion of the observed type preserves contextual equivalence. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesObservationalLaws.

Theorem closed_observational_type_conversion : forall A B t u,
  closed_observational_eq A t u -> type_wf empty_ctx B -> conv A B ->
  closed_observational_eq B t u.
Proof.
  intros A B t u HE [k HB] HAB.
  destruct (proj1 (closed_observational_function_tests _ _ _) HE) as [HT [HU Htest]].
  destruct (named_type_correctness _ _ _ HT) as [j HA].
  apply (proj2 (closed_observational_function_tests _ _ _)); split.
  - eapply ty_conv; [exact HT|exact HB|exact HAB].
  - split; [eapply ty_conv; [exact HU|exact HB|exact HAB]|].
    intros f r HF HR; apply Htest; [|exact HR].
    eapply ty_conv; [exact HF| |].
    + eapply arrow_formation; [exact named_weakening|exact HA|apply observation_formation, wf_nil].
    + apply arrow_conversion; auto using cv_sym, cv_refl.
Qed.

Theorem observational_type_conversion : forall Gamma A B t u,
  observational_eq Gamma A t u -> type_wf Gamma B -> conv A B ->
  observational_eq Gamma B t u.
Proof.
  intros Gamma A B t u [HT [HU Hobs]] [k HB] HAB.
  split; [eapply ty_conv; [exact HT|exact HB|exact HAB]|].
  split; [eapply ty_conv; [exact HU|exact HB|exact HAB]|].
  intros env HE; eapply closed_observational_type_conversion.
  - exact (Hobs env HE).
  - exists k; pose proof (named_closing_substitution _ _ _ _ HE HB) as H.
    now rewrite instantiate_sort in H.
  - now apply instantiate_conversion.
Qed.

Theorem closed_observational_application : forall A B f g a b,
  closed_observational_eq (arrow A B) f g -> closed_observational_eq A a b ->
  closed_observational_eq B (TApp f a) (TApp g b).
Proof.
  intros A B f g a b HF HA.
  destruct HF as [Hf [Hg Hfg]], HA as [Ha [Hb Hab]].
  pose proof (arrow_apply_regular named_type_correctness _ _ _ _ _ Hf Ha) as Hfa.
  destruct (named_type_correctness _ _ _ Hf) as [j Hfun].
  destruct (named_type_correctness _ _ _ Hfa) as [k HB].
  assert (HC : typing (extend empty_ctx 0 (arrow A B)) (TApp (TVar 0) a) B).
  { eapply arrow_apply_regular; [exact named_type_correctness| |].
    - apply ty_var; [eapply wf_cons; [apply wf_nil|exact Hfun|reflexivity]|apply lookup_extend_same].
    - eapply named_weakening; [reflexivity|exact Ha|exact Hfun]. }
  assert (HE : closed_observational_eq (arrow A B) f g) by (split; [exact Hf|split; assumption]).
  pose proof (closed_observational_context _ _ _ _ _ _ _ HB HC HE) as H.
  change (closed_observational_eq B (TApp f (subst f 0 a)) (TApp g (subst g 0 a))) in H.
  rewrite !subst_fresh in H by (rewrite (typed_closed _ _ Ha); tauto).
  eapply closed_observational_trans; [exact H|].
  eapply closed_observational_congruence; [exact Hg|split; [exact Ha|split; assumption]].
Qed.

Print Assumptions closed_observational_type_conversion.
Print Assumptions observational_type_conversion.
Print Assumptions closed_observational_application.
