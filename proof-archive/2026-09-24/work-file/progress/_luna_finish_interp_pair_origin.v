Require Import Progress SignatureLemmas.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
Import Progress._work_cjoin Progress._work_cstep_invariants
  Progress._work_conv_whd_pos Progress._tmp_commute Progress.MuApplicationSort.

Lemma eval_interp_luna : forall D D' X,
    eval D D' -> eval (TInterp D X) (TInterp D' X).
Proof.
  intros D D' X H. induction H.
  - apply ev_refl.
  - eapply ev_step; [apply st_interp1; exact H | exact IHeval].
Qed.

Lemma eval_trans_luna : forall t u v,
    eval t u -> eval u v -> eval t v.
Proof.
  intros t u v H. induction H; intros Huv.
  - exact Huv.
  - eapply ev_step; [exact H | apply IHeval; exact Huv].
Qed.

Lemma erased_pair_interp_prod_origin : forall a b T D X A B,
    check [] (TPair a b) T ->
    cjoin (phi_erase T) (phi_erase (TInterp D X)) ->
    eval D (TIProd A B) ->
    exists TA TB,
      check [] a TA /\ check [] b TB /\
      cjoin (phi_erase TA) (phi_erase (TInterp A X)) /\
      cjoin (phi_erase TB) (phi_erase (TInterp B X)).
Proof.
  intros a b T D X A B Hcheck Hjoin Heval.
  destruct (pair_origin [] a b T Hcheck)
    as [TA [B0 [Ha [Hb Hconv]]]].
  pose proof (conv_phi_cjoin _ _ Hconv) as Hpi.
  pose proof (cjoin_trans _ _ _ Hpi Hjoin) as Hsig.
  pose proof (eval_interp_luna D (TIProd A B) X Heval) as HevalI.
  assert (HevalStep : eval (TInterp (TIProd A B) X)
      (TSigma (TInterp A X) (lift 1 0 (TInterp B X)))).
  { eapply ev_step; [eapply st_interp_prod; eauto using pstep_refl | apply ev_refl]. }
  pose proof (eval_trans_luna _ _ _ HevalI HevalStep) as Heval'.
  pose proof (phi_erase_eval_csteps _ _ Heval') as Hred.
  destruct (cjoin_reduce_right _ _ _ Hsig Hred) as [w [Hw1 Hw2]].
  destruct (cjoin_sigma_inv_luna _ _ _ _ (ex_intro _ w (conj Hw1 Hw2)))
    as [HAjoin HBjoin].
  assert (Hsub : cjoin
        (subst (phi_erase a) 0 (phi_erase B0))
        (subst (phi_erase a) 0
          (phi_erase (lift 1 0 (TInterp B X))))).
  { unfold cjoin in HBjoin. destruct HBjoin as [q [HL HR]].
    exists (subst (phi_erase a) 0 q). split;
      [eapply rtc_cstep_subst_luna; exact HL
      |eapply rtc_cstep_subst_luna; exact HR]. }
  cbn [phi_erase] in Hsub.
  rewrite phi_erase_lift in Hsub.
  rewrite subst_lift_zero in Hsub.
  assert (Hsub' : cjoin (phi_erase (subst a 0 B0))
      (phi_erase (TInterp B X))).
  { rewrite phi_erase_subst. exact Hsub. }
  exists TA, (subst a 0 B0). repeat split; assumption.
Qed.

Print Assumptions erased_pair_interp_prod_origin.

Lemma erased_pair_interp_choice_origin : forall a b T D X E F,
    check [] (TPair a b) T ->
    cjoin (phi_erase T) (phi_erase (TInterp D X)) ->
    eval D (TIChoice E F) ->
    exists TA TB,
      check [] a TA /\ check [] b TB /\
      cjoin (phi_erase TA) (phi_erase (TEnumT E)) /\
      cjoin (phi_erase TB) (phi_erase (TInterp (TApp F a) X)).
Proof.
  intros a b T D X E F Hcheck Hjoin Heval.
  destruct (pair_origin [] a b T Hcheck)
    as [TA [B0 [Ha [Hb Hconv]]]].
  pose proof (conv_phi_cjoin _ _ Hconv) as Hpi.
  pose proof (cjoin_trans _ _ _ Hpi Hjoin) as Hsig.
  pose proof (eval_interp_luna D (TIChoice E F) X Heval) as HevalI.
  assert (HevalStep : eval (TInterp (TIChoice E F) X)
      (TSigma (TEnumT E)
        (TInterp (TApp (lift 1 0 F) (TVar 0)) (lift 1 0 X)))).
  { eapply ev_step; [eapply st_interp_choice | apply ev_refl]. }
  pose proof (eval_trans_luna _ _ _ HevalI HevalStep) as Heval'.
  pose proof (phi_erase_eval_csteps _ _ Heval') as Hred.
  destruct (cjoin_reduce_right _ _ _ Hsig Hred) as [w [Hw1 Hw2]].
  destruct (cjoin_sigma_inv_luna _ _ _ _ (ex_intro _ w (conj Hw1 Hw2)))
    as [HAjoin HBjoin].
  assert (Hsub : cjoin
      (subst (phi_erase a) 0 (phi_erase B0))
      (subst (phi_erase a) 0
        (phi_erase (TInterp (TApp (lift 1 0 F) (TVar 0))
          (lift 1 0 X))))).
  { unfold cjoin in HBjoin. destruct HBjoin as [q [HL HR]].
    exists (subst (phi_erase a) 0 q). split;
      [eapply rtc_cstep_subst_luna; exact HL
      |eapply rtc_cstep_subst_luna; exact HR]. }
  cbn [phi_erase subst] in Hsub.
  rewrite phi_erase_lift in Hsub.
  rewrite subst_lift_zero in Hsub.
  cbn in Hsub.
  rewrite Progress._tmp_commute.lift_zero_id_local in Hsub.
  rewrite phi_erase_lift in Hsub.
  rewrite subst_lift_zero in Hsub.
  assert (Hsub' : cjoin (phi_erase (subst a 0 B0))
      (phi_erase (TInterp (TApp F a) X))).
  { rewrite phi_erase_subst. exact Hsub. }
  exists TA, (subst a 0 B0). repeat split; assumption.
Qed.

Print Assumptions erased_pair_interp_choice_origin.
