Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.
Require Import _luna_repair_spine.

Lemma spine_phi_mem_join_live : forall c L1,
    spine_mem c L1 -> forall Sf i L2 L3,
    spine_phi Sf i L2 L3 -> pjoin L1 L2 ->
    (forall d, conv c d ->
      ~ desc_against (TApp (branches (TApp Sf i)) d)) ->
    spine_mem c L3.
Proof.
  intros c L1 Hmem.
  induction Hmem as [Phi A c' Phi' Heval Hcc | Phi A c' Phi' Heval Htail IH];
    intros Sf i L2 L3 Hphi Hjoin Live;
    pose proof (pjoin_eval_left _ _ _ Hjoin Heval) as Hleft;
    inversion Hphi; subst.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [Hlabels _]].
    eapply sm_here; [apply ev_refl |].
    eapply cv_trans; [exact Hcc | apply pjoin_conv; exact Hlabels].
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [Hlabels _]].
    exfalso. eapply Live; [|exact H0].
    eapply cv_trans; [exact Hcc | apply pjoin_conv; exact Hlabels].
  - exfalso. eapply (luna_no_pjoin_lcons_neutral _ _ _ _ H0).
    eapply pjoin_eval_right; eassumption.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [_ Htails]].
    eapply sm_there; [apply ev_refl |].
    eapply IH; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [_ Htails]].
    eapply IH; eassumption.
  - exfalso. eapply (luna_no_pjoin_lcons_neutral _ _ _ _ H0).
    eapply pjoin_eval_right; eassumption.
Qed.

Lemma spine_phi_mem_live : forall Sf i Phi Psi c,
    spine_phi Sf i Phi Psi -> spine_mem c Phi ->
    (forall d, conv c d ->
      ~ desc_against (TApp (branches (TApp Sf i)) d)) ->
    spine_mem c Psi.
Proof.
  intros; eapply spine_phi_mem_join_live; eauto using pjoin_refl.
Qed.

Print Assumptions spine_phi_mem_join_live.
Print Assumptions spine_phi_mem_live.
