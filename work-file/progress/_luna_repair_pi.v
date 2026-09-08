Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Lemma epstep_conv_mut_luna :
    (forall t u, epstep t u -> conv t u) /\
    (forall bs bs', epbranches bs bs' -> forall pre M Q,
        conv (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply epstep_epbranches_ind; intros;
    try solve [eauto 12 using cv_refl, cv_pi, cv_lam, cv_app, cv_sigma,
      cv_pair, cv_fst, cv_snd, cv_conse, cv_enumt, cv_esucc, cv_epi,
      cv_switch, cv_idesc, cv_ivar, cv_iprod, cv_ipi, cv_isig, cv_ichoice,
      cv_interp, cv_mui, cv_mus, cv_in, cv_ind, cv_iall, cv_hyps,
      cv_list, cv_lnil, cv_lcons].
  - eapply cv_trans.
    + apply (H1 [] M Q).
    + apply cv_case; [exact H | exact H0].
  - eapply cv_trans; [apply cv_eta | assumption].
  - eapply cv_trans.
    + apply cv_case_br; [exact H | exact H0].
    + specialize (H1 (pre ++ [(c',b')]) M Q).
      repeat rewrite <- app_assoc in H1. cbn in H1. exact H1.
Qed.

Lemma epstep_conv_luna : forall t u, epstep t u -> conv t u.
Proof. exact (proj1 epstep_conv_mut_luna). Qed.

Lemma rtc_pstep_conv_luna : forall t u, rtc pstep t u -> conv t u.
Proof.
  intros t u H. induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply pstep_conv, H | exact IHrtc].
Qed.

Lemma rtc_epstep_conv_luna : forall t u, rtc epstep t u -> conv t u.
Proof.
  intros t u H. induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply epstep_conv_luna, H | exact IHrtc].
Qed.

Lemma cstep_conv_luna : forall t u, cstep t u -> conv t u.
Proof.
  intros t u H. destruct H.
  - apply rtc_pstep_conv_luna, H.
  - apply rtc_epstep_conv_luna, H.
Qed.

Lemma rtc_cstep_conv_luna : forall t u, rtc cstep t u -> conv t u.
Proof.
  intros t u H. induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply cstep_conv_luna, H | exact IHrtc].
Qed.

Lemma cjoin_conv_luna : forall t u, cjoin t u -> conv t u.
Proof.
  intros t u [w [Htw Huw]].
  eapply cv_trans;
    [apply rtc_cstep_conv_luna, Htw | apply cv_sym, rtc_cstep_conv_luna, Huw].
Qed.

Lemma fconv_pi_sort_codomain_luna : forall A0 A1 B1 j,
    fconv (TPi A0 (TSort j)) (TPi A1 B1) ->
    conv B1 (TSort j).
Proof.
  intros A0 A1 B1 j H.
  destruct (fconv_cjoin _ _ H) as [w [H0 H1]].
  destruct (rtc_cstep_pi_inv _ _ _ H0)
    as [Aw [Bw [Hw0 Hd0]]].
  destruct (rtc_cstep_pi_inv _ _ _ H1)
    as [Aw' [Bw' [Hw1 Hd1]]].
  rewrite Hw0 in Hw1. inversion Hw1; subst.
  destruct Hd0 as [_ Hd0].
  destruct Hd1 as [_ Hd1].
  pose proof (rtc_cstep_sort_id j Bw' Hd0) as ->.
  apply cjoin_conv_luna.
  exists (TSort j). split.
  - exact Hd1.
  - apply rtc_refl.
Qed.

Print Assumptions fconv_pi_sort_codomain_luna.
