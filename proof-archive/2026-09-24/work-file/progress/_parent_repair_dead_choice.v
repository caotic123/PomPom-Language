Require Import Progress _luna_repair_pair_origin _luna_repair_sigma_join.
From Stdlib Require Import List.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Lemma eval_interp_description_parent : forall D D' X,
  eval D D' -> eval (TInterp D X) (TInterp D' X).
Proof.
  intros D D' X HE. induction HE.
  - apply ev_refl.
  - eapply ev_step; [apply st_interp1; exact H | exact IHHE].
Qed.

Lemma empty_choice_domain_parent : forall a b D X E F,
  check [] (TPair a b) (TInterp D X) ->
  eval D (TIChoice E F) -> eval E TNilE ->
  exists A, check [] a A /\
    cjoin (phi_erase A) (TEnumT TNilE).
Proof.
  intros a b D X E F HC HD HE.
  destruct (pair_origin _ _ _ _ HC) as [A [B [HA [HB Hconv]]]].
  exists A. split; [exact HA |].
  assert (HI : conv (TInterp D X)
    (TSigma (TEnumT E)
      (TInterp (TApp (lift 1 0 F) (TVar 0)) (lift 1 0 X)))).
  { eapply cv_trans.
    - apply cv_interp; [apply conv_of_eval; exact HD | apply cv_refl].
    - apply cv_step, st_interp_choice. }
  pose proof (conv_phi_cjoin _ _ (cv_trans Hconv HI)) as HJ.
  cbn [phi_erase] in HJ.
  destruct (cjoin_sigma_inv_luna _ _ _ _ HJ) as [HJdom _].
  eapply cjoin_trans; [exact HJdom |].
  change (cjoin (phi_erase (TEnumT E)) (phi_erase (TEnumT TNilE))).
  apply conv_phi_cjoin, cv_enumt, conv_of_eval, HE.
Qed.

Print Assumptions empty_choice_domain_parent.

Lemma empty_choice_pair_parent : forall xs D X E F,
  check [] xs (TInterp D X) -> value xs ->
  eval D (TIChoice E F) -> exists a b, xs = TPair a b.
Proof.
  intros xs D X E F HC HV HD.
  assert (HW : whd (TInterp D X) HSigma).
  { eexists. split.
    - eapply eval_trans.
      + apply eval_interp_description_parent; exact HD.
      + eapply ev_step; [apply st_interp_choice | apply ev_refl].
    - constructor. }
  exact (canon_main [] xs _ HC eq_refl HV _ HSigma (cv_refl _) HW).
Qed.

Print Assumptions empty_choice_pair_parent.

Require Import _luna_repair_empty_enum_check.

Lemma dead_choice_nil_progress_parent : forall xs D X E F,
  check [] xs (TInterp D X) -> value xs ->
  eval D (TIChoice E F) -> eval E TNilE ->
  (forall a b A, xs = TPair a b -> check [] a A ->
     value a \/ exists a', step a a') ->
  exists xs', step xs xs'.
Proof.
  intros xs D X E F HC HV HD HE IH.
  destruct (empty_choice_pair_parent _ _ _ _ _ HC HV HD) as [a [b ->]].
  destruct (empty_choice_domain_parent _ _ _ _ _ _ HC HD HE) as [A [HA HJ]].
  destruct (IH a b A eq_refl HA) as [HVa | [a' Hstep]].
  - exfalso. exact (erased_empty_check_value_luna [] a A HA eq_refl HVa HJ).
  - exists (TPair a' b). apply st_pair1, Hstep.
Qed.

Print Assumptions dead_choice_nil_progress_parent.
