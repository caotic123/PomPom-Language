From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Progress.
Import TypeRules.

Lemma pbranches_refl : forall bs, pbranches bs bs.
Proof.
  induction bs as [|[c b] bs IH].
  - constructor.
  - constructor; try apply pstep_refl; exact IH.
Qed.

Lemma pbranches_replace_label : forall bs1 c c' b bs2,
    pstep c c' ->
    pbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c',b) :: bs2).
Proof.
  induction bs1 as [|[d e] bs1 IH]; intros c c' b bs2 Hcc'; cbn.
  - constructor; [exact Hcc'|apply pstep_refl|apply pbranches_refl].
  - constructor; [apply pstep_refl|apply pstep_refl|apply IH; exact Hcc'].
Qed.

Lemma step_pstep : forall t u, step t u -> pstep t u.
Proof.
  intros t u H.
  induction H;
    try solve [constructor; eauto using pstep_refl];
    try solve [eapply ps_case; eauto using pstep_refl, pbranches_refl];
    try solve [eapply ps_case; eauto using pstep_refl, pbranches_replace_label];
    try solve [eapply ps_case_red; eauto using pstep_refl].
  - eapply ps_fst_pair; eauto using pstep_refl.
  - eapply ps_snd_pair; eauto using pstep_refl.
  - eapply ps_epi_nil; eauto using pstep_refl.
  - eapply ps_epi_cons; eauto using pstep_refl.
  - eapply ps_switch_zero; eauto using pstep_refl.
  - eapply ps_switch_succ; eauto using pstep_refl.
  - eapply ps_interp_one; eauto using pstep_refl.
  - eapply ps_iall_var; eauto using pstep_refl.
  - eapply ps_iall_one; eauto using pstep_refl.
  - eapply ps_iall_sig; eauto using pstep_refl.
  - eapply ps_iall_choice; eauto using pstep_refl.
  - eapply ps_hyps_var; eauto using pstep_refl.
  - eapply ps_hyps_one; eauto using pstep_refl.
  - eapply ps_hyps_pi; eauto using pstep_refl.
  - eapply ps_hyps_sig; eauto using pstep_refl.
  - eapply ps_hyps_choice; eauto using pstep_refl.
Qed.
