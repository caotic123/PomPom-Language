(* Combined paths preserve the inert Unit and Pair heads. *)

Require Import Progress _tmp_epstep _work_mixed_closure.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma rtc_pstep_unit_id_parent : forall u,
    rtc pstep TUnit u -> u = TUnit.
Proof.
  intros u H. remember TUnit as t eqn:Ht.
  induction H; subst; [reflexivity |].
  inversion H; subst. apply IHrtc. reflexivity.
Qed.

Lemma rtc_epstep_unit_id_parent : forall u,
    rtc epstep TUnit u -> u = TUnit.
Proof.
  intros u H. remember TUnit as t eqn:Ht.
  induction H; subst; [reflexivity |].
  inversion H; subst. apply IHrtc. reflexivity.
Qed.

Lemma cstep_unit_id_parent : forall u, cstep TUnit u -> u = TUnit.
Proof.
  intros u H. inversion H; subst.
  - eapply rtc_pstep_unit_id_parent; eassumption.
  - eapply rtc_epstep_unit_id_parent; eassumption.
Qed.

Lemma rtc_cstep_unit_id_parent : forall u,
    rtc cstep TUnit u -> u = TUnit.
Proof.
  intros u H. remember TUnit as t eqn:Ht.
  induction H; subst; [reflexivity |].
  pose proof (cstep_unit_id_parent _ H) as Hy. subst y.
  apply IHrtc. reflexivity.
Qed.

Corollary rtc_cstep_unit_not_sort_parent : forall j,
    ~ rtc cstep TUnit (TSort j).
Proof.
  intros j H. discriminate (rtc_cstep_unit_id_parent _ H).
Qed.

Lemma pstep_pair_inv_parent : forall a b u,
    pstep (TPair a b) u ->
    exists a' b', u = TPair a' b' /\ pstep a a' /\ pstep b b'.
Proof.
  intros a b u H. inversion H; subst.
  eexists; eexists. repeat split; try reflexivity; eassumption.
Qed.

Lemma rtc_pstep_pair_inv_parent : forall a b u,
    rtc pstep (TPair a b) u ->
    exists a' b', u = TPair a' b' /\
      rtc pstep a a' /\ rtc pstep b b'.
Proof.
  intros a b u H. remember (TPair a b) as t eqn:Ht. revert a b Ht.
  induction H; intros a0 b0 Heq; subst.
  - exists a0, b0. repeat split; apply rtc_refl.
  - destruct (pstep_pair_inv_parent _ _ _ H)
      as [a1 [b1 [-> [Ha1 Hb1]]]].
    destruct (IHrtc a1 b1 eq_refl)
      as [a2 [b2 [-> [Ha2 Hb2]]]].
    exists a2, b2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_pair_inv_parent : forall a b u,
    epstep (TPair a b) u ->
    exists a' b', u = TPair a' b' /\ epstep a a' /\ epstep b b'.
Proof.
  intros a b u H. inversion H; subst.
  eexists; eexists. repeat split; try reflexivity; eassumption.
Qed.

Lemma rtc_epstep_pair_inv_parent : forall a b u,
    rtc epstep (TPair a b) u ->
    exists a' b', u = TPair a' b' /\
      rtc epstep a a' /\ rtc epstep b b'.
Proof.
  intros a b u H. remember (TPair a b) as t eqn:Ht. revert a b Ht.
  induction H; intros a0 b0 Heq; subst.
  - exists a0, b0. repeat split; apply rtc_refl.
  - destruct (epstep_pair_inv_parent _ _ _ H)
      as [a1 [b1 [-> [Ha1 Hb1]]]].
    destruct (IHrtc a1 b1 eq_refl)
      as [a2 [b2 [-> [Ha2 Hb2]]]].
    exists a2, b2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_pair_inv_parent : forall a b u,
    cstep (TPair a b) u -> exists a' b', u = TPair a' b'.
Proof.
  intros a b u H. inversion H; subst.
  - destruct (rtc_pstep_pair_inv_parent _ _ _ H0)
      as [a' [b' [-> _]]]. eauto.
  - destruct (rtc_epstep_pair_inv_parent _ _ _ H0)
      as [a' [b' [-> _]]]. eauto.
Qed.

Lemma rtc_cstep_pair_inv_parent : forall a b u,
    rtc cstep (TPair a b) u -> exists a' b', u = TPair a' b'.
Proof.
  intros a b u H. remember (TPair a b) as t eqn:Ht. revert a b Ht.
  induction H; intros a0 b0 Heq; subst.
  - eauto.
  - destruct (cstep_pair_inv_parent _ _ _ H) as [a1 [b1 ->]].
    exact (IHrtc a1 b1 eq_refl).
Qed.

Corollary rtc_cstep_pair_not_sort_parent : forall a b j,
    ~ rtc cstep (TPair a b) (TSort j).
Proof.
  intros a b j H.
  destruct (rtc_cstep_pair_inv_parent _ _ _ H) as [a' [b' Heq]].
  discriminate Heq.
Qed.

Print Assumptions rtc_cstep_unit_not_sort_parent.
Print Assumptions rtc_cstep_pair_not_sort_parent.
