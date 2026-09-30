Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _luna_parallel_hshape _luna_rtc_epbranches_nth.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma rtc_pstep_hshape : forall t u,
    rtc pstep t u -> forall h, hshape t h -> hshape u h.
Proof.
  intros t u H. induction H; intros h Hshape.
  - exact Hshape.
  - apply IHrtc. eapply pstep_hshape_luna; eassumption.
Qed.

Lemma rtc_epstep_hshape : forall t u,
    rtc epstep t u -> forall h, hshape t h -> hshape u h.
Proof.
  intros t u H. induction H; intros h Hshape.
  - exact Hshape.
  - apply IHrtc. eapply epstep_hshape_luna; eassumption.
Qed.

Lemma cstep_hshape : forall t u,
    cstep t u -> forall h, hshape t h -> hshape u h.
Proof.
  intros t u H h Hshape. destruct H.
  - eapply rtc_pstep_hshape; eassumption.
  - eapply rtc_epstep_hshape; eassumption.
Qed.

Lemma rtc_cstep_hshape : forall t u,
    rtc cstep t u -> forall h, hshape t h -> hshape u h.
Proof.
  intros t u H. induction H; intros h Hshape.
  - exact Hshape.
  - apply IHrtc. eapply cstep_hshape; eassumption.
Qed.

Lemma pstep_enumt_inv_local : forall E u, pstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ pstep E E'.
Proof. intros E u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_enumt_inv : forall E u, rtc pstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ rtc pstep E E'.
Proof.
  intros E u H. remember (TEnumT E) as t eqn:Ht. revert E Ht.
  induction H; intros E HE; subst.
  - exists E. split; [reflexivity | apply rtc_refl].
  - destruct (pstep_enumt_inv_local E y H) as [E1 [-> HE1]].
    destruct (IHrtc E1 eq_refl) as [E2 [-> HE2]].
    exists E2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Lemma epstep_enumt_inv_local : forall E u, epstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ epstep E E'.
Proof. intros E u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_enumt_inv : forall E u, rtc epstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ rtc epstep E E'.
Proof.
  intros E u H. remember (TEnumT E) as t eqn:Ht. revert E Ht.
  induction H; intros E HE; subst.
  - exists E. split; [reflexivity | apply rtc_refl].
  - destruct (epstep_enumt_inv_local E y H) as [E1 [-> HE1]].
    destruct (IHrtc E1 eq_refl) as [E2 [-> HE2]].
    exists E2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Lemma cstep_enumt_inv : forall E u, cstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ cstep E E'.
Proof.
  intros E u H. inversion H; subst.
  - destruct (rtc_pstep_enumt_inv _ _ H0) as [E' [-> HE']].
    exists E'. split; [reflexivity | apply cs_core, HE'].
  - destruct (rtc_epstep_enumt_inv _ _ H0) as [E' [-> HE']].
    exists E'. split; [reflexivity | apply cs_eta, HE'].
Qed.

Lemma rtc_cstep_enumt_inv : forall E u, rtc cstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ rtc cstep E E'.
Proof.
  intros E u H. remember (TEnumT E) as t eqn:Ht. revert E Ht.
  induction H; intros E HE; subst.
  - exists E. split; [reflexivity | apply rtc_refl].
  - destruct (cstep_enumt_inv E y H) as [E1 [-> HE1]].
    destruct (IHrtc E1 eq_refl) as [E2 [-> HE2]].
    exists E2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Lemma pstep_pi_inv_local : forall A B u, pstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_pi_inv : forall A B u, rtc pstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TPi A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_pi_inv_local A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_pi_inv_local : forall A B u, epstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_pi_inv : forall A B u, rtc epstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TPi A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_pi_inv_local A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_pi_inv : forall A B u, cstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_pi_inv _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_pi_inv _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_pi_inv : forall A B u, rtc cstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TPi A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_pi_inv A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_pi_inv : forall A1 B1 A2 B2,
    cjoin (TPi A1 B1) (TPi A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_pi_inv _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_pi_inv _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.

Lemma rtc_pstep_sort_id : forall k u,
    rtc pstep (TSort k) u -> u = TSort k.
Proof.
  intros k u H. remember (TSort k) as t eqn:Ht.
  induction H; subst; [reflexivity |].
  inversion H; subst. apply IHrtc. reflexivity.
Qed.

Lemma rtc_epstep_sort_id : forall k u,
    rtc epstep (TSort k) u -> u = TSort k.
Proof.
  intros k u H. remember (TSort k) as t eqn:Ht.
  induction H; subst; [reflexivity |].
  inversion H; subst. apply IHrtc. reflexivity.
Qed.

Lemma cstep_sort_id : forall k u, cstep (TSort k) u -> u = TSort k.
Proof.
  intros k u H. inversion H; subst.
  - eapply rtc_pstep_sort_id, H0.
  - eapply rtc_epstep_sort_id, H0.
Qed.

Lemma rtc_cstep_sort_id : forall k u,
    rtc cstep (TSort k) u -> u = TSort k.
Proof.
  intros k u H. remember (TSort k) as t eqn:Ht.
  induction H.
  - now inversion Ht.
  - subst x.
    assert (Hy : y = TSort k) by (eapply cstep_sort_id; eassumption).
    subst y. apply IHrtc. reflexivity.
Qed.

Lemma rtc_pstep_enum_pos_id : forall c d n,
    rtc pstep c d -> enum_pos c n -> d = c.
Proof.
  intros c d n H. revert n.
  induction H; intros n Hpos; [reflexivity |].
  assert (Hyx : y = x) by (eapply pstep_enum_pos_id; eassumption).
  subst y. rewrite (IHrtc n Hpos). reflexivity.
Qed.

Lemma cstep_enum_pos_id : forall c d n,
    cstep c d -> enum_pos c n -> d = c.
Proof.
  intros c d n H Hpos. destruct H.
  - eapply rtc_pstep_enum_pos_id; eassumption.
  - eapply rtc_epstep_enum_pos_id_luna; eassumption.
Qed.

Lemma rtc_cstep_enum_pos_id : forall c d n,
    rtc cstep c d -> enum_pos c n -> d = c.
Proof.
  intros c d n H. revert n.
  induction H; intros n Hpos; [reflexivity |].
  assert (Hyx : y = x) by (eapply cstep_enum_pos_id; eassumption).
  subst y. rewrite (IHrtc n Hpos). reflexivity.
Qed.
