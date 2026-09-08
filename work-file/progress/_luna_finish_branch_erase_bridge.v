Require Import Progress ErasureCounterexample SignatureLemmas.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Lemma phi_branch_erase_bridge_luna : forall t,
    phi_erase (branch_erase t) = phi_erase t.
Proof.
  apply (tsize_strong_ind (fun t =>
    phi_erase (branch_erase t) = phi_erase t)).
  intros t IH. destruct t; cbn [branch_erase phi_erase].
  all: repeat match goal with
  | |- context [phi_erase (branch_erase ?x)] =>
      rewrite (IH x ltac:(cbn; lia))
  end; try reflexivity.
  - rewrite map_map. f_equal.
    apply map_ext_in. intros [c b] Hin. cbn.
    rewrite (IH c ltac:(eapply tsize_case_bs; exact Hin)).
    rewrite (IH b ltac:(eapply tsize_case_bs_body; exact Hin)).
    reflexivity.
Qed.

Print Assumptions phi_branch_erase_bridge_luna.

Lemma epstep_conv_bridge_mut :
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
  - eapply cv_trans; [apply (H1 [] M Q) | apply cv_case; [exact H | exact H0]].
  - eapply cv_trans; [apply cv_eta | assumption].
  - eapply cv_trans; [apply cv_case_br; [exact H | exact H0] |].
    specialize (H1 (pre ++ [(c',b')]) M Q).
    repeat rewrite <- app_assoc in H1. cbn in H1. exact H1.
Qed.

Lemma epstep_conv_bridge : forall t u, epstep t u -> conv t u.
Proof. exact (proj1 epstep_conv_bridge_mut). Qed.

Lemma rtc_pstep_conv_bridge : forall t u, rtc pstep t u -> conv t u.
Proof. intros t u H; induction H; [apply cv_refl|eapply cv_trans; [apply pstep_conv; exact H|exact IHrtc]]. Qed.

Lemma rtc_epstep_conv_bridge : forall t u, rtc epstep t u -> conv t u.
Proof. intros t u H; induction H; [apply cv_refl|eapply cv_trans; [apply epstep_conv_bridge; exact H|exact IHrtc]]. Qed.

Lemma cstep_conv_bridge : forall t u, cstep t u -> conv t u.
Proof. intros t u H; destruct H as [x y Hp|x y He]; [apply rtc_pstep_conv_bridge; exact Hp|apply rtc_epstep_conv_bridge; exact He]. Qed.

Lemma rtc_cstep_conv_bridge : forall t u, rtc cstep t u -> conv t u.
Proof. intros t u H; induction H; [apply cv_refl|eapply cv_trans; [apply cstep_conv_bridge; exact H|exact IHrtc]]. Qed.

Lemma cjoin_conv_bridge : forall t u, cjoin t u -> conv t u.
Proof. intros t u [w [H1 H2]]; eapply cv_trans; [apply rtc_cstep_conv_bridge; exact H1|apply cv_sym; apply rtc_cstep_conv_bridge; exact H2]. Qed.

Lemma cjoin_branch_to_phi_luna : forall t u,
    cjoin (branch_erase t) (branch_erase u) ->
    cjoin (phi_erase t) (phi_erase u).
Proof.
  intros t u H.
  pose proof (cjoin_conv_bridge _ _ H) as Hconv.
  pose proof (conv_phi_cjoin _ _ Hconv) as Hphi.
  rewrite (phi_branch_erase_bridge_luna t) in Hphi.
  rewrite (phi_branch_erase_bridge_luna u) in Hphi.
  exact Hphi.
Qed.

Print Assumptions cjoin_branch_to_phi_luna.
