(* General eta preservation derived from annotated strengthening.
   There is no restriction on the shape of the contracted function. *)
Require Export annotated.AStrengthening annotated.AGeneration annotated.AEta.

Theorem eta_preservation : forall Gamma A B C D f T,
  typing Gamma (TLam A B (TApp C D (lift 1 0 f) (TVar 0))) T ->
  typing Gamma f T.
Proof.
  intros Gamma A B C D f T HT.
  destruct (lambda_generation _ _ _ HT _ _ _ eq_refl)
    as [j [k [HA [HB [Hbody Hout]]]]].
  destruct (application_generation _ _ _ Hbody _ _ _ _ eq_refl)
    as [l [m [HC [HD [Hf [Hx Happ]]]]]].
  destruct (typing_strengthening_comparison _ _ _ Hf 0 Gamma f
    (insert_head _ _) (typing_context _ _ _ HT) eq_refl)
    as [S [HS Hfun]].
  destruct (RC.comparison_pi_source _ _ Hfun _ _ (RCore.cv_refl _))
    as [U [V Hview]].
  pose proof (RS.conversion_subst _ _ Hview Raw.TUnit 0) as HSview.
  cbn [Raw.subst] in HSview; rewrite RB.subst_lift_cancel in HSview.
  assert (Hfun' : RC.type_comparison
    (Raw.TPi (Raw.lift 1 0 (Raw.subst Raw.TUnit 0 U))
      (Raw.lift 1 1 (Raw.subst Raw.TUnit 1 V)))
    (Raw.TPi (erase C) (erase D))).
  { eapply RC.comparison_left_conversion; [exact Hfun|].
    apply RCore.cv_sym; exact (RW.conversion_lift _ _ HSview 1 0). }
  destruct (RC.comparison_pi_inversion _ _ _ _ Hfun') as [Hdom Hcod].
  destruct (RCh.variable_change_generation _ _ _ (typing_erasure _ _ _ Hx) _ eq_refl)
    as [A0 [HA0 Harg]].
  cbn in HA0; inversion HA0; subst A0.
  assert (Hdomain : RC.type_comparison (erase A) (Raw.subst Raw.TUnit 0 U)).
  { apply comparison_unlift with (c := 0).
    eapply RC.comparison_transitive; [exact (RC.type_change_comparison _ _ _ Harg)|exact Hdom]. }
  pose proof (RC.comparison_subst _ _ Hcod (Raw.TVar 0) 0) as Hcodomain.
  rewrite RB.subst_eta_beta_cancel in Hcodomain.
  assert (Hpi : RC.type_comparison
    (Raw.TPi (Raw.subst Raw.TUnit 0 U) (Raw.subst Raw.TUnit 1 V))
    (Raw.TPi (erase A) (erase B))).
  { eapply RC.cmp_pi; [apply RCore.cv_refl|apply RCore.cv_refl|exact Hdomain|].
    eapply RC.comparison_transitive; [exact Hcodomain|exact Happ]. }
  eapply comparison_typing; [exact HS| |exact (type_correctness _ _ _ HT)].
  eapply RC.comparison_transitive; [|exact Hout].
  eapply RC.comparison_left_conversion; [exact Hpi|exact HSview].
Qed.

Theorem eta_root_preservation : forall Gamma t u T,
  typing Gamma t T -> eta_root t u -> typing Gamma u T.
Proof. intros Gamma t u T HT HR; destruct HR; eapply eta_preservation; exact HT. Qed.

Theorem eta_contract_preservation : forall Gamma t u T,
  typing Gamma t T -> eta_contract t = Some u -> typing Gamma u T.
Proof.
  intros Gamma t u T HT HR; eapply eta_root_preservation;
    [exact HT|now apply eta_contract_sound].
Qed.

Print Assumptions eta_preservation.
Print Assumptions eta_root_preservation.
Print Assumptions eta_contract_preservation.
