Require Import Progress SignatureLemmas.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
Import Progress._work_cjoin Progress._work_cstep_invariants.

Lemma spine_phi_mem_join_or_luna : forall c L1,
    spine_mem c L1 -> forall S i L2 L3 (P : Prop),
    spine_phi S i L2 L3 -> pjoin L1 L2 ->
    (forall d, conv c d ->
      desc_against (TApp (branches (TApp S i)) d) -> P) ->
    spine_mem c L3 \/ P.
Proof.
  intros c L1 Hmem.
  induction Hmem as [Phi A c' Phi' Heval Hcc | Phi A c' Phi' Heval Htail IH];
    intros S i L2 L3 P Hphi Hjoin HP;
    pose proof (pjoin_eval_left _ _ _ Hjoin Heval) as Hleft;
    inversion Hphi; subst.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [Hlabels _]].
    left. eapply sm_here; [apply ev_refl |].
    eapply cv_trans; [exact Hcc | apply pjoin_conv; exact Hlabels].
  - right. eapply HP; [|exact H0].
    pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [Hlabels _]].
    eapply cv_trans; [exact Hcc | apply pjoin_conv; exact Hlabels].
  - exfalso. eapply (luna_no_pjoin_lcons_neutral _ _ _ _ H0).
    eapply pjoin_eval_right; eassumption.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [_ Htails]].
    destruct (IH S i _ _ P ltac:(eassumption) Htails HP) as [Hm | Hp].
    + left. eapply sm_there; [apply ev_refl | exact Hm].
    + right; exact Hp.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [_ Htails]].
    destruct (IH S i _ _ P ltac:(eassumption) Htails HP) as [Hm | Hp].
    + left; exact Hm.
    + right; exact Hp.
  - exfalso. eapply (luna_no_pjoin_lcons_neutral _ _ _ _ H0).
    eapply pjoin_eval_right; eassumption.
Qed.

Lemma spine_phi_mem_or_luna : forall S i Phi Psi c,
    spine_phi S i Phi Psi -> spine_mem c Phi -> forall P : Prop,
    (forall d, conv c d ->
      desc_against (TApp (branches (TApp S i)) d) -> P) ->
    spine_mem c Psi \/ P.
Proof.
  intros; eapply spine_phi_mem_join_or_luna; eauto using pjoin_refl.
Qed.

Print Assumptions spine_phi_mem_join_or_luna.
Print Assumptions spine_phi_mem_or_luna.
