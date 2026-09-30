(* Regression checks for function cumulativity and eta contraction.
   The pre-repair counterexample is preserved in proof-archive. *)
From Stdlib Require Import List Arith Bool Lia.
Require Import OpenSignaturesTypingEncoding OpenSignaturesLabels.
Import ListNotations.

Definition eta_context := extend empty_ctx 0 (arrow TUnitT (TSort 0)).
Definition eta_source := TLam 1 (TApp (TVar 0) (TVar 1)).
Definition eta_type := arrow TUnitT (TSort 1).

Lemma eta_context_wf : wf eta_context.
Proof.
  eapply wf_cons with (k:=1); [constructor| |reflexivity].
  exact (arrow_formation named_weakening empty_ctx TUnitT (TSort 0) 0 1 (ty_unitT 0 wf_nil) (ty_sort 0 wf_nil)).
Qed.
Lemma eta_source_typing : typing eta_context eta_source eta_type.
Proof.
  pose proof eta_context_wf as Hctx.
  assert (HA : typing eta_context TUnitT (TSort 0)) by now apply ty_unitT.
  assert (HB : typing eta_context (TSort 1) (TSort 2)) by now apply ty_sort.
  assert (Hpi : typing eta_context eta_type (TSort 2))
    by (exact (arrow_formation named_weakening _ _ _ 0 2 HA HB)).
  assert (Hx : fresh_in eta_context 1) by reflexivity.
  assert (Hext : wf (extend eta_context 1 TUnitT)) by (eapply wf_cons; eassumption).
  change (typing eta_context (TLam 1 (TApp (TVar 0) (TVar 1))) (TPi 1 TUnitT (TSort 1))).
  eapply ty_lam; [exact Hx|exact Hpi|].
  apply ty_cumul with (j:=0); [|lia].
  eapply arrow_app with (A:=TUnitT) (B:=TSort 0) (j:=0) (k:=1).
  - exact named_weakening.
  - now apply ty_unitT.
  - now apply ty_sort.
  - apply ty_var; [exact Hext|reflexivity].
  - apply ty_var; [exact Hext|reflexivity].
Qed.
Lemma eta_source_reduction : reduction eta_source (TVar 0).
Proof. apply red_eta;cbn;intuition discriminate. Qed.

Lemma eta_reduct_typing : typing eta_context (TVar 0) eta_type.
Proof.
  eapply ty_cumul_fun with (B:=TSort 0) (j:=1) (k:=2).
  - apply ty_var; [exact eta_context_wf|reflexivity].
  - exact (arrow_formation named_weakening _ _ _ 0 1
      (ty_unitT 0 eta_context_wf) (ty_sort 0 eta_context_wf)).
  - exact (arrow_formation named_weakening _ _ _ 0 2
      (ty_unitT 0 eta_context_wf) (ty_sort 1 eta_context_wf)).
  - apply ul_refl.
  - apply ul_sort; lia.
Qed.

Theorem eta_cumulativity_regression :
  typing eta_context eta_source eta_type /\ reduction eta_source (TVar 0) /\
  typing eta_context (TVar 0) eta_type.
Proof. repeat split; auto using eta_source_typing, eta_source_reduction, eta_reduct_typing. Qed.

Definition domain_context := extend empty_ctx 0 (arrow (TSort 1) (TSort 0)).
Definition domain_type := arrow (TSort 0) (TSort 0).

Lemma domain_context_wf : wf domain_context.
Proof.
  eapply wf_cons with (k:=2); [constructor| |reflexivity].
  exact (arrow_formation named_weakening _ _ _ 2 1 (ty_sort 1 wf_nil) (ty_sort 0 wf_nil)).
Qed.
Lemma domain_eta_source_typing : typing domain_context eta_source domain_type.
Proof.
  pose proof domain_context_wf as Hctx.
  assert (Hx : fresh_in domain_context 1) by reflexivity.
  assert (Hext : wf (extend domain_context 1 (TSort 0))) by
    (eapply wf_cons; [exact Hctx|now apply ty_sort|exact Hx]).
  eapply ty_lam with (k:=1).
  - exact Hx.
  - exact (arrow_formation named_weakening _ _ _ 1 1 (ty_sort 0 Hctx) (ty_sort 0 Hctx)).
  - eapply arrow_app with (A:=TSort 1) (B:=TSort 0) (j:=2) (k:=1).
    + exact named_weakening.
    + now apply ty_sort.
    + now apply ty_sort.
    + apply ty_var; [exact Hext|reflexivity].
    + eapply ty_cumul with (j:=0); [apply ty_var; [exact Hext|reflexivity]|lia].
Qed.
Lemma domain_eta_reduct_typing : typing domain_context (TVar 0) domain_type.
Proof.
  eapply ty_cumul_fun with (A:=TSort 1) (B:=TSort 0) (j:=2) (k:=1).
  - apply ty_var; [exact domain_context_wf|reflexivity].
  - exact (arrow_formation named_weakening _ _ _ 2 1
      (ty_sort 1 domain_context_wf) (ty_sort 0 domain_context_wf)).
  - exact (arrow_formation named_weakening _ _ _ 1 1
      (ty_sort 0 domain_context_wf) (ty_sort 0 domain_context_wf)).
  - apply ul_sort; lia.
  - apply ul_refl.
Qed.
Theorem eta_domain_regression :
  typing domain_context eta_source domain_type /\ reduction eta_source (TVar 0) /\
  typing domain_context (TVar 0) domain_type.
Proof. repeat split; auto using domain_eta_source_typing, eta_source_reduction, domain_eta_reduct_typing. Qed.

Definition dependent_function k := TPi 1 (TSort 0) (TPi 2 (TVar 1) (TSort k)).
Lemma dependent_function_formed : forall k,
  typing empty_ctx (dependent_function k) (TSort (S k)).
Proof.
  intro k.
  assert (Hctx : wf (extend empty_ctx 1 (TSort 0))) by
    (eapply wf_cons; [constructor|apply ty_sort; constructor|reflexivity]).
  assert (Hv : typing (extend empty_ctx 1 (TSort 0)) (TVar 1) (TSort 0)) by
    (apply ty_var; [exact Hctx|reflexivity]).
  assert (Hctx' : wf (extend (extend empty_ctx 1 (TSort 0)) 2 (TVar 1))) by
    (eapply wf_cons; [exact Hctx|exact Hv|reflexivity]).
  replace (S k) with (Nat.max 1 (S k)) at 1 by lia.
  eapply ty_pi; [reflexivity|apply ty_sort;constructor|].
  change (TSort (S k)) with (TSort (Nat.max 0 (S k))).
  eapply ty_pi; [reflexivity|exact Hv|now apply ty_sort].
Qed.

Definition dependent_context := extend empty_ctx 0 (dependent_function 0).
Theorem nested_dependent_cumulativity :
  typing dependent_context (TVar 0) (dependent_function 1).
Proof.
  assert (Hctx : wf dependent_context) by
    (eapply wf_cons; [constructor|apply dependent_function_formed|reflexivity]).
  assert (Hform : forall k, typing dependent_context (dependent_function k) (TSort (S k))).
  { intro k. eapply named_weakening; [reflexivity|apply dependent_function_formed|apply dependent_function_formed]. }
  eapply ty_cumul_fun with (B:=TPi 2 (TVar 1) (TSort 0)) (j:=1) (k:=2).
  - apply ty_var; [exact Hctx|reflexivity].
  - exact (Hform 0).
  - exact (Hform 1).
  - apply ul_refl.
  - apply ul_pi; [apply ul_refl|apply ul_sort; lia].
Qed.

Lemma sorts_remain_distinct : ~ conv (TSort 0) (TSort 1).
Proof.
  intro HC. destruct (raw_conversion_joinability _ _ HC) as [w [w' [Hw [Hw' Ha]]]].
  apply reduces_sort in Hw; apply reduces_sort in Hw'; subst; discriminate.
Qed.
Lemma universes_do_not_lower : ~ universe_le (TSort 1) (TSort 0).
Proof. intro H; inversion H; lia. Qed.

Print Assumptions eta_cumulativity_regression.
Print Assumptions eta_domain_regression.
Print Assumptions nested_dependent_cumulativity.
Print Assumptions sorts_remain_distinct.
