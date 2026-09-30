From Stdlib Require Import List Arith Bool Lia.
Require Import OpenSignaturesTypingEncoding OpenSignaturesLabels.
Import ListNotations.

Lemma variable_pi_type : forall Gamma t A, typing Gamma t A -> forall n B,
  t = TVar n -> lookup Gamma n = Some B -> term_head B = Some h_pi -> conv B A.
Proof.
  intros Gamma t A H; induction H; intros v T Heq Hlookup Hhead; try discriminate.
  - inversion Heq; subst. rewrite H0 in Hlookup; inversion Hlookup; subst; apply cv_refl.
  - subst u. unfold alpha_equiv, alpha_eqb in H0; destruct t;
      cbn [alpha_eqb_in alpha_var] in H0; try discriminate.
    apply Nat.eqb_eq in H0; subst. eapply IHtyping; eassumption || reflexivity.
  - eapply cv_trans; [eapply IHtyping1;eassumption|eassumption].
  - pose proof (IHtyping _ _ Heq Hlookup Hhead) as HC.
    exfalso; pose proof (raw_head _ _ _ _ HC Hhead eq_refl); discriminate.
Qed.

Lemma pi_sort_levels : forall x y A B j k,
  conv (TPi x A (TSort j)) (TPi y B (TSort k)) -> j = k.
Proof.
  intros x y A B j k HC.
  destruct (raw_conversion_joinability _ _ HC) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_pi _ _ _ _ Hw) as [A' [C [-> [HA HC']]]].
  destruct (reduces_pi _ _ _ _ Hw') as [B' [D [-> [HB HD]]]].
  apply reduces_sort in HC'; apply reduces_sort in HD; subst C D.
  unfold alpha_equiv, alpha_eqb in Ha; cbn [alpha_eqb_in] in Ha.
  apply Bool.andb_true_iff in Ha; destruct Ha as [_ Heq]. now apply Nat.eqb_eq.
Qed.

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
Lemma eta_reduct_not_typed : ~ typing eta_context (TVar 0) eta_type.
Proof.
  intro H. pose proof (variable_pi_type _ _ _ H 0 (arrow TUnitT (TSort 0)) eq_refl eq_refl eq_refl) as HC.
  apply pi_sort_levels in HC; discriminate.
Qed.
Theorem eta_preservation_counterexample :
  typing eta_context eta_source eta_type /\ reduction eta_source (TVar 0) /\
  ~ typing eta_context (TVar 0) eta_type.
Proof. repeat split; auto using eta_source_typing, eta_source_reduction, eta_reduct_not_typed. Qed.

Print Assumptions eta_preservation_counterexample.
