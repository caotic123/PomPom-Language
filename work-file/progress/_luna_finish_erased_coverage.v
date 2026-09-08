Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants
  Progress._work_conv_whd_pos.

Lemma pstep_lcons_inv_luna : forall A c L u, pstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ pstep A A' /\ pstep c c' /\ pstep L L'.
Proof. intros A c L u H; inversion H; subst; do 3 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma rtc_pstep_lcons_inv_luna : forall A c L u, rtc pstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ rtc pstep A A' /\ rtc pstep c c' /\ rtc pstep L L'.
Proof.
 intros A c L u H; remember (TLCons A c L) as t eqn:E; revert A c L E.
 induction H; intros; subst; [exists A,c,L; repeat split; apply rtc_refl|].
 destruct (pstep_lcons_inv_luna _ _ _ _ H) as [A1 [c1 [L1 [-> [HA [Hc HL]]]]]].
 destruct (IHrtc A1 c1 L1 eq_refl) as [A2 [c2 [L2 [-> [HA2 [Hc2 HL2]]]]]].
 exists A2,c2,L2; repeat split; eauto using rtc_step.
Qed.
Lemma epstep_lcons_inv_luna : forall A c L u, epstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ epstep A A' /\ epstep c c' /\ epstep L L'.
Proof. intros A c L u H; inversion H; subst; do 3 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma rtc_epstep_lcons_inv_luna : forall A c L u, rtc epstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ rtc epstep A A' /\ rtc epstep c c' /\ rtc epstep L L'.
Proof.
 intros A c L u H; remember (TLCons A c L) as t eqn:E; revert A c L E.
 induction H; intros; subst; [exists A,c,L; repeat split; apply rtc_refl|].
 destruct (epstep_lcons_inv_luna _ _ _ _ H) as [A1 [c1 [L1 [-> [HA [Hc HL]]]]]].
 destruct (IHrtc A1 c1 L1 eq_refl) as [A2 [c2 [L2 [-> [HA2 [Hc2 HL2]]]]]].
 exists A2,c2,L2; repeat split; eauto using rtc_step.
Qed.
Lemma cstep_lcons_inv_luna : forall A c L u, cstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ cstep A A' /\ cstep c c' /\ cstep L L'.
Proof.
 intros; inversion H; subst.
 - destruct (rtc_pstep_lcons_inv_luna _ _ _ _ H0) as [A' [c' [L' [-> [HA [Hc HL]]]]]].
   exists A',c',L'; repeat split; apply cs_core; assumption.
 - destruct (rtc_epstep_lcons_inv_luna _ _ _ _ H0) as [A' [c' [L' [-> [HA [Hc HL]]]]]].
   exists A',c',L'; repeat split; apply cs_eta; assumption.
Qed.
Lemma rtc_cstep_lcons_inv_luna : forall A c L u, rtc cstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ rtc cstep A A' /\ rtc cstep c c' /\ rtc cstep L L'.
Proof.
 intros A c L u H; remember (TLCons A c L) as t eqn:E; revert A c L E.
 induction H; intros; subst; [exists A,c,L; repeat split; apply rtc_refl|].
 destruct (cstep_lcons_inv_luna _ _ _ _ H) as [A1 [c1 [L1 [-> [HA [Hc HL]]]]]].
 destruct (IHrtc A1 c1 L1 eq_refl) as [A2 [c2 [L2 [-> [HA2 [Hc2 HL2]]]]]].
 exists A2,c2,L2; repeat split; eauto using rtc_step.
Qed.
Lemma cjoin_lcons_inv_erased_luna : forall A c L B d R,
 cjoin (TLCons A c L) (TLCons B d R) -> cjoin A B /\ cjoin c d /\ cjoin L R.
Proof.
 intros A c L B d R [w [H1 H2]].
 destruct (rtc_cstep_lcons_inv_luna _ _ _ _ H1) as [A1 [c1 [L1 [Hw1 [HA1 [Hc1 HL1]]]]]].
 rewrite Hw1 in H2.
 destruct (rtc_cstep_lcons_inv_luna B d R (TLCons A1 c1 L1) H2) as [A2 [c2 [L2 [Hw2 [HA2 [Hc2 HL2]]]]]].
 inversion Hw2; subst A2 c2 L2. repeat split; unfold cjoin; eauto.
Qed.
Print Assumptions cjoin_lcons_inv_erased_luna.

Lemma pstep_lnil_inv_luna : forall B u, pstep (TLNil B) u ->
  exists B', u = TLNil B' /\ pstep B B'.
Proof. intros B u H; inversion H; subst; eexists; split; try reflexivity; eassumption. Qed.
Lemma rtc_pstep_lnil_inv_luna : forall B u, rtc pstep (TLNil B) u ->
  exists B', u = TLNil B' /\ rtc pstep B B'.
Proof.
 intros B u H; remember (TLNil B) as t eqn:E; revert B E.
 induction H; intros; subst; [exists B; split; [reflexivity|apply rtc_refl]|].
 destruct (pstep_lnil_inv_luna _ _ H) as [B1 [-> HB1]].
 destruct (IHrtc B1 eq_refl) as [B2 [-> HB2]].
 exists B2; split; [reflexivity|eauto using rtc_step].
Qed.
Lemma epstep_lnil_inv_luna : forall B u, epstep (TLNil B) u ->
  exists B', u = TLNil B' /\ epstep B B'.
Proof. intros B u H; inversion H; subst; eexists; split; try reflexivity; eassumption. Qed.
Lemma rtc_epstep_lnil_inv_luna : forall B u, rtc epstep (TLNil B) u ->
  exists B', u = TLNil B' /\ rtc epstep B B'.
Proof.
 intros B u H; remember (TLNil B) as t eqn:E; revert B E.
 induction H; intros; subst; [exists B; split; [reflexivity|apply rtc_refl]|].
 destruct (epstep_lnil_inv_luna _ _ H) as [B1 [-> HB1]].
 destruct (IHrtc B1 eq_refl) as [B2 [-> HB2]].
 exists B2; split; [reflexivity|eauto using rtc_step].
Qed.
Lemma cstep_lnil_inv_luna : forall B u, cstep (TLNil B) u ->
  exists B', u = TLNil B' /\ cstep B B'.
Proof.
 intros B u H; inversion H; subst.
 - destruct (rtc_pstep_lnil_inv_luna _ _ H0) as [B' [-> HB']]; exists B'; split; [reflexivity|apply cs_core; exact HB'].
 - destruct (rtc_epstep_lnil_inv_luna _ _ H0) as [B' [-> HB']]; exists B'; split; [reflexivity|apply cs_eta; exact HB'].
Qed.
Lemma rtc_cstep_lnil_shape : forall B u, rtc cstep (TLNil B) u ->
  exists B', u = TLNil B'.
Proof.
 intros B u H; remember (TLNil B) as t eqn:E; revert B E.
 induction H; intros; subst; [exists B; reflexivity|].
 destruct (cstep_lnil_inv_luna _ _ H) as [B1 [-> HB1]].
 destruct (IHrtc B1 eq_refl) as [B2 ->]. exists B2; reflexivity.
Qed.
Lemma no_cjoin_lcons_lnil_luna : forall A c L B,
  ~ cjoin (TLCons A c L) (TLNil B).
Proof.
 intros A c L B [w [H1 H2]].
 destruct (rtc_cstep_lcons_inv_luna _ _ _ _ H1) as [A1 [c1 [L1 [Hw1 _]]]].
 destruct (rtc_cstep_lnil_shape _ _ H2) as [B' Hw2].
 rewrite Hw1 in Hw2. discriminate Hw2.
Qed.
Print Assumptions no_cjoin_lcons_lnil_luna.

Lemma erased_spine_covered : forall c L1,
  spine_mem c L1 -> forall L2 bs, covers bs L2 ->
  cjoin (phi_erase L1) (phi_erase L2) ->
  exists d, In d bs /\ cjoin (phi_erase c) (phi_erase d).
Proof.
  intros c L1 Hmem.
  induction Hmem as [Phi A c' Phi' Heval Hcc | Phi A c' Phi' Heval Htail IH];
    intros L2 bs Hcov Hjoin.
  - pose proof (phi_erase_eval_csteps _ _ Heval) as Hleft.
    destruct (cjoin_reduce_left _ _ _ Hjoin Hleft) as [w [Hw1 Hw2]].
    inversion Hcov; subst.
    + exfalso.
      pose proof (phi_erase_eval_csteps _ _ H) as Hright.
      destruct (cjoin_reduce_right _ _ _ (ex_intro _ w (conj Hw1 Hw2)) Hright) as [z [Hz1 Hz2]].
      cbn in Hz1, Hz2.
      apply (no_cjoin_lcons_lnil_luna (phi_erase A) (phi_erase c')
        (phi_erase Phi') (phi_erase A0)).
      exact (ex_intro _ z (conj Hz1 Hz2)).
    + pose proof (phi_erase_eval_csteps _ _ H) as Hright.
      destruct (cjoin_reduce_right _ _ _ (ex_intro _ w (conj Hw1 Hw2)) Hright)
        as [z [Hz1 Hz2]].
      destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ (ex_intro _ z (conj Hz1 Hz2)))
        as [_ [Hcd _]].
      apply Exists_exists in H0. destruct H0 as [d [Hd Hconv]].
      exists d; split; [exact Hd|].
      eapply cjoin_trans; [apply conv_phi_cjoin; exact Hcc|].
      eapply cjoin_trans; [exact Hcd|].
      apply conv_phi_cjoin; exact Hconv.
  - pose proof (phi_erase_eval_csteps _ _ Heval) as Hleft.
    destruct (cjoin_reduce_left _ _ _ Hjoin Hleft) as [w [Hw1 Hw2]].
    inversion Hcov; subst.
    + exfalso.
      pose proof (phi_erase_eval_csteps _ _ H) as Hright.
      destruct (cjoin_reduce_right _ _ _ (ex_intro _ w (conj Hw1 Hw2)) Hright) as [z [Hz1 Hz2]].
      cbn in Hz1, Hz2.
      apply (no_cjoin_lcons_lnil_luna (phi_erase A) (phi_erase c')
        (phi_erase Phi') (phi_erase A0)).
      exact (ex_intro _ z (conj Hz1 Hz2)).
    + pose proof (phi_erase_eval_csteps _ _ H) as Hright.
      destruct (cjoin_reduce_right _ _ _ (ex_intro _ w (conj Hw1 Hw2)) Hright)
        as [z [Hz1 Hz2]].
      destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ (ex_intro _ z (conj Hz1 Hz2)))
        as [_ [_ Htailjoin]].
      eapply IH; eassumption.
Qed.

Print Assumptions erased_spine_covered.

Lemma erased_spine_covered_pos : forall c n L1 L2 bs,
  enum_pos c n ->
  Forall (fun d => exists m, enum_pos d m) bs ->
  spine_mem c L1 -> covers bs L2 -> conv L1 L2 ->
  exists d, In d bs /\ enum_pos d n.
Proof.
  intros c n L1 L2 bs Hc Hbs Hmem Hcov Hconv.
  destruct (erased_spine_covered c L1 Hmem L2 bs Hcov
      (conv_phi_cjoin _ _ Hconv)) as [d [Hd Hcd]].
  rewrite Forall_forall in Hbs.
  destruct (Hbs d Hd) as [m Hdm].
  pose proof (phi_erase_enum_pos _ _ Hc) as Hec.
  pose proof (phi_erase_enum_pos _ _ Hdm) as Hed.
  destruct Hcd as [w [Hcw Hdw]].
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hcw Hec) as Hwc.
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hdw Hed) as Hwd.
  subst w.
  exists d. split; [exact Hd|].
  assert (Hmn : m = n).
  { eapply enum_pos_functional; [exact Hed |].
    rewrite <- Hwd. exact Hec. }
  subst m. exact Hdm.
Qed.

Print Assumptions erased_spine_covered_pos.
