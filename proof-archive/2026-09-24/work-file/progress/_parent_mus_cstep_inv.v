(* The bare TMuS head is preserved by every combined reduction path. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cstep_invariants.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma pstep_mus_inv_parent : forall S u,
    pstep (TMuS S) u -> exists S', u = TMuS S' /\ pstep S S'.
Proof.
  intros S u H. inversion H; subst.
  eexists. split; [reflexivity | eassumption].
Qed.

Lemma rtc_pstep_mus_inv_parent : forall S u,
    rtc pstep (TMuS S) u ->
    exists S', u = TMuS S' /\ rtc pstep S S'.
Proof.
  intros S u H. remember (TMuS S) as t eqn:Ht. revert S Ht.
  induction H; intros S0 Heq; subst.
  - exists S0. split; [reflexivity | apply rtc_refl].
  - destruct (pstep_mus_inv_parent _ _ H) as [S1 [-> HS1]].
    destruct (IHrtc S1 eq_refl) as [S2 [-> HS2]].
    exists S2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Lemma epstep_mus_inv_parent : forall S u,
    epstep (TMuS S) u -> exists S', u = TMuS S' /\ epstep S S'.
Proof.
  intros S u H. inversion H; subst.
  eexists. split; [reflexivity | eassumption].
Qed.

Lemma rtc_epstep_mus_inv_parent : forall S u,
    rtc epstep (TMuS S) u ->
    exists S', u = TMuS S' /\ rtc epstep S S'.
Proof.
  intros S u H. remember (TMuS S) as t eqn:Ht. revert S Ht.
  induction H; intros S0 Heq; subst.
  - exists S0. split; [reflexivity | apply rtc_refl].
  - destruct (epstep_mus_inv_parent _ _ H) as [S1 [-> HS1]].
    destruct (IHrtc S1 eq_refl) as [S2 [-> HS2]].
    exists S2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Lemma cstep_mus_inv_parent : forall S u,
    cstep (TMuS S) u -> exists S', u = TMuS S' /\ cstep S S'.
Proof.
  intros S u H. inversion H; subst.
  - destruct (rtc_pstep_mus_inv_parent _ _ H0) as [S' [-> HS']].
    exists S'. split; [reflexivity | apply cs_core; exact HS'].
  - destruct (rtc_epstep_mus_inv_parent _ _ H0) as [S' [-> HS']].
    exists S'. split; [reflexivity | apply cs_eta; exact HS'].
Qed.

Lemma rtc_cstep_mus_inv_parent : forall S u,
    rtc cstep (TMuS S) u ->
    exists S', u = TMuS S' /\ rtc cstep S S'.
Proof.
  intros S u H. remember (TMuS S) as t eqn:Ht. revert S Ht.
  induction H; intros S0 Heq; subst.
  - exists S0. split; [reflexivity | apply rtc_refl].
  - destruct (cstep_mus_inv_parent _ _ H) as [S1 [-> HS1]].
    destruct (IHrtc S1 eq_refl) as [S2 [-> HS2]].
    exists S2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Corollary rtc_cstep_mus_not_sort_parent : forall S j,
    ~ rtc cstep (TMuS S) (TSort j).
Proof.
  intros S j H.
  destruct (rtc_cstep_mus_inv_parent _ _ H) as [S' [Heq _]].
  discriminate Heq.
Qed.

Corollary rtc_cstep_musapp_not_sort_parent : forall S i j,
    ~ rtc cstep (TApp (TMuS S) i) (TSort j).
Proof.
  intros S i j H.
  pose proof (rtc_cstep_hshape _ _ H HMuSApp (hs_musapp S i)) as Hshape.
  inversion Hshape.
Qed.

Print Assumptions rtc_cstep_mus_inv_parent.
Print Assumptions rtc_cstep_mus_not_sort_parent.
Print Assumptions rtc_cstep_musapp_not_sort_parent.
