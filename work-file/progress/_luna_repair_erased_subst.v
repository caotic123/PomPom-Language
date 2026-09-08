Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._tmp_epstep_subst Progress._work_cjoin Progress._work_cstep_invariants.

Lemma rtc_epstep_subst_luna : forall t t' a k,
    rtc epstep t t' ->
    rtc epstep (subst a k t) (subst a k t').
Proof.
  intros t t' a k Ht. induction Ht as [x | x y z Hxy Hyz IH].
  - apply rtc_refl.
  - eapply rtc_step.
    + eapply epstep_subst; [exact Hxy | apply epstep_refl].
    + exact IH.
Qed.

Lemma rtc_pstep_subst_luna : forall t t' a k,
    rtc pstep t t' ->
    rtc pstep (subst a k t) (subst a k t').
Proof.
  intros t t' a k Ht. induction Ht as [x | x y z Hxy Hyz IH].
  - apply rtc_refl.
  - eapply rtc_step; [eapply pstep_subst; [exact Hxy | apply pstep_refl] | exact IH].
Qed.

Lemma rtc_cstep_subst_luna : forall t t' a k,
    rtc cstep t t' ->
    rtc cstep (subst a k t) (subst a k t').
Proof.
  intros t t' a k Ht. induction Ht as [x | x y z Hxy Hyz IH].
  - apply rtc_refl.
  - eapply rtc_step.
    + destruct Hxy as [Hp | He].
      * apply cs_core. eapply rtc_pstep_subst_luna; exact r.
      * apply cs_eta. eapply rtc_epstep_subst_luna; exact r.
    + exact IH.
Qed.

Lemma erased_sort_cjoin_subst_luna : forall B a j,
    cjoin (phi_erase B) (TSort j) ->
    cjoin (phi_erase (subst a 0 B)) (TSort j).
Proof.
  intros B a j [w [HB Hw]].
  pose proof (rtc_cstep_sort_id j w Hw) as ->.
  rewrite phi_erase_subst.
  assert (Hs : rtc cstep
      (subst (phi_erase a) 0 (phi_erase B))
      (subst (phi_erase a) 0 (TSort j))).
  { eapply rtc_cstep_subst_luna; exact HB. }
  cbn [subst] in Hs.
  exists (TSort j). split; [exact Hs | apply rtc_refl].
Qed.

Print Assumptions rtc_pstep_subst_luna.
Print Assumptions rtc_cstep_subst_luna.
Print Assumptions erased_sort_cjoin_subst_luna.
