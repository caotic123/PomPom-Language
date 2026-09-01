Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.
Import TypeRules.

Ltac conv_congr :=
  eauto 12 using cv_refl, cv_pi, cv_lam, cv_app, cv_sigma, cv_pair,
    cv_fst, cv_snd, cv_conse, cv_enumt, cv_esucc, cv_epi, cv_switch,
    cv_idesc, cv_ivar, cv_iprod, cv_ipi, cv_isig, cv_ichoice,
    cv_interp, cv_mui, cv_mus, cv_in, cv_ind, cv_iall, cv_hyps,
    cv_list, cv_lnil, cv_lcons.

Lemma try_pstep_conv_mut :
  (forall t u (H : pstep t u), conv t u) /\
  (forall bs bs' (H : pbranches bs bs'), forall pre M Q,
      conv (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply pstep_pbranches_ind; intros;
    try solve [conv_congr].
  all: try solve
    [eapply cv_trans; [conv_congr | apply cv_step; constructor]].
  - eapply cv_trans.
    + eapply cv_case; eauto.
    + specialize (H1 [] M' Q'). cbn in H1. exact H1.
  - eapply cv_trans with (u := TApp (TLam b') a');
      [conv_congr | apply cv_step, st_beta].
  - eapply cv_trans with (u := TFst (TPair a' b'));
      [conv_congr | apply cv_step, st_fst].
  - eapply cv_trans with (u := TSnd (TPair a' b'));
      [conv_congr | apply cv_step, st_snd].
  - eapply cv_trans with (u := TEPi (TConsE tg' E') P');
      [conv_congr | apply cv_step, st_epi_cons].
  - eapply cv_trans with
      (u := TSwitch (TConsE tg' E') P' (TPair p0' ps') TEZero);
      [conv_congr | apply cv_step, st_switch_zero].
  - eapply cv_trans with
      (u := TSwitch (TConsE tg' E') P' (TPair p0' ps') (TESucc n'));
      [conv_congr | apply cv_step, st_switch_succ].
  - eapply cv_trans with (u := TInterp (TIVar i') X');
      [conv_congr | apply cv_step, st_interp_var].
  - eapply cv_trans with (u := TInterp (TIProd A' B') X');
      [conv_congr | apply cv_step, st_interp_prod].
  - eapply cv_trans with (u := TInterp (TIPi S' T') X');
      [conv_congr | apply cv_step, st_interp_pi].
  - eapply cv_trans with (u := TInterp (TISig S' T') X');
      [conv_congr | apply cv_step, st_interp_sig].
  - eapply cv_trans with (u := TInterp (TIChoice E' T') X');
      [conv_congr | apply cv_step, st_interp_choice].
  - eapply cv_trans with (u := TIAll (TIVar j') X' x' P');
      [conv_congr | apply cv_step, st_iall_var].
  - eapply cv_trans with
      (u := TIAll (TIProd A' B') X' (TPair a' b') P');
      [conv_congr | apply cv_step, st_iall_prod].
  - eapply cv_trans with (u := TIAll (TIPi S' T') X' f' P');
      [conv_congr | apply cv_step, st_iall_pi].
  - eapply cv_trans with
      (u := TIAll (TISig S' T') X' (TPair s' x') P');
      [conv_congr | apply cv_step, st_iall_sig].
  - eapply cv_trans with
      (u := TIAll (TIChoice E' T') X' (TPair e' x') P');
      [conv_congr | apply cv_step, st_iall_choice].
  - eapply cv_trans with (u := THyps (TIVar j') X' P' h' x');
      [conv_congr | apply cv_step, st_hyps_var].
  - eapply cv_trans with
      (u := THyps (TIProd A' B') X' P' h' (TPair a' b'));
      [conv_congr | apply cv_step, st_hyps_prod].
  - eapply cv_trans with (u := THyps (TIPi S' T') X' P' h' f');
      [conv_congr | apply cv_step, st_hyps_pi].
  - eapply cv_trans with
      (u := THyps (TISig S' T') X' P' h' (TPair s' x'));
      [conv_congr | apply cv_step, st_hyps_sig].
  - eapply cv_trans with
      (u := THyps (TIChoice E' T') X' P' h' (TPair e' x'));
      [conv_congr | apply cv_step, st_hyps_choice].
  - eapply cv_trans with (u := TInd R' P' s' i' (TIn xs'));
      [conv_congr | apply cv_step, st_ind].
  - assert (Hk : k < length bs).
    { apply nth_error_Some. rewrite e. discriminate. }
    pose proof (firstn_skipn_middle k bs e) as Hsplit.
    rewrite <- Hsplit in e2 |- *.
    eapply cv_trans.
    + eapply cv_case; [|apply cv_refl].
      apply cv_in, cv_pair; [apply cv_refl | exact H].
    + eapply cv_trans.
      * apply cv_case_br; [apply cv_refl | exact H0].
      * apply cv_step.
        eapply st_case with (k:=k) (c:=c) (b:=b') (n:=n).
        -- rewrite nth_error_app2; [|rewrite firstn_length; lia].
           rewrite firstn_length, Nat.min_l by lia.
           replace (k - k) with 0 by lia. reflexivity.
        -- exact e0.
        -- exact e1.
        -- intros j cj bj Hj Hnth.
           eapply e2; [exact Hj |].
           rewrite nth_error_app1 in Hnth
             by (rewrite firstn_length, Nat.min_l by lia; exact Hj).
           rewrite nth_error_app1
             by (rewrite firstn_length, Nat.min_l by lia; exact Hj).
           exact Hnth.
  - change (conv
      (TCase M Q (pre ++ (c,b) :: bs))
      (TCase M Q (pre ++ (c',b') :: bs'))).
    eapply cv_trans.
    + apply cv_case_br; eauto.
    + specialize (H1 (pre ++ [(c',b')]) M Q).
      repeat rewrite <- app_assoc in H1. cbn in H1. exact H1.
Qed.
