Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Lemma pstep_sigma_inv_luna : forall A B u, pstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_sigma_inv_luna : forall A B u, rtc pstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TSigma A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_sigma_inv_luna A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_sigma_inv_luna : forall A B u, epstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_sigma_inv_luna : forall A B u, rtc epstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TSigma A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_sigma_inv_luna A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_sigma_inv_luna : forall A B u, cstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_sigma_inv_luna _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_sigma_inv_luna _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_sigma_inv_luna : forall A B u, rtc cstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TSigma A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_sigma_inv_luna A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_sigma_inv_luna : forall A1 B1 A2 B2,
    cjoin (TSigma A1 B1) (TSigma A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_sigma_inv_luna _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_sigma_inv_luna _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.

Print Assumptions cjoin_sigma_inv_luna.
