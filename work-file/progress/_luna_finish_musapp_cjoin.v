Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules Progress._tmp_epstep Progress._work_mixed_closure
  Progress._work_cjoin Progress._work_cstep_invariants.

Lemma pstep_mus_inv_luna : forall S u, pstep (TMuS S) u ->
  exists S', u = TMuS S' /\ pstep S S'.
Proof. intros; inversion H; subst; eexists; split; [reflexivity|eassumption]. Qed.
Lemma epstep_mus_inv_luna : forall S u, epstep (TMuS S) u ->
  exists S', u = TMuS S' /\ epstep S S'.
Proof. intros; inversion H; subst; eexists; split; [reflexivity|eassumption]. Qed.

Lemma pstep_musapp_inv_luna : forall S i u, pstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ pstep S S' /\ pstep i i'.
Proof. intros S i u H; inversion H; subst.
  destruct (pstep_mus_inv_luna _ _ H2) as [S' [-> HS']].
  exists S', a'. repeat split; assumption. Qed.
Lemma rtc_pstep_musapp_inv_luna : forall S i u, rtc pstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ rtc pstep S S' /\ rtc pstep i i'.
Proof.
 intros S i u H; remember (TApp (TMuS S) i) as t eqn:E; revert S i E.
 induction H; intros; subst; [exists S,i; repeat split; apply rtc_refl|].
 destruct (pstep_musapp_inv_luna _ _ _ H) as [S1 [i1 [-> [HS Hi]]]].
 destruct (IHrtc S1 i1 eq_refl) as [S2 [i2 [-> [HS2 Hi2]]]].
 exists S2,i2; repeat split; eauto using rtc_step.
Qed.
Lemma epstep_musapp_inv_luna : forall S i u, epstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ epstep S S' /\ epstep i i'.
Proof. intros S i u H; inversion H; subst.
  destruct (epstep_mus_inv_luna _ _ H2) as [S' [-> HS']].
  exists S', a'. repeat split; assumption. Qed.
Lemma rtc_epstep_musapp_inv_luna : forall S i u, rtc epstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ rtc epstep S S' /\ rtc epstep i i'.
Proof.
 intros S i u H; remember (TApp (TMuS S) i) as t eqn:E; revert S i E.
 induction H; intros; subst; [exists S,i; repeat split; apply rtc_refl|].
 destruct (epstep_musapp_inv_luna _ _ _ H) as [S1 [i1 [-> [HS Hi]]]].
 destruct (IHrtc S1 i1 eq_refl) as [S2 [i2 [-> [HS2 Hi2]]]].
 exists S2,i2; repeat split; eauto using rtc_step.
Qed.
Lemma cstep_musapp_inv_luna : forall S i u, cstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ cstep S S' /\ cstep i i'.
Proof.
 intros S i u H; inversion H; subst.
 - destruct (rtc_pstep_musapp_inv_luna _ _ _ H0) as [S' [i' [-> [HS Hi]]]].
   exists S',i'; repeat split; apply cs_core; assumption.
 - destruct (rtc_epstep_musapp_inv_luna _ _ _ H0) as [S' [i' [-> [HS Hi]]]].
   exists S',i'; repeat split; apply cs_eta; assumption.
Qed.
Lemma rtc_cstep_musapp_inv_luna : forall S i u, rtc cstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ rtc cstep S S' /\ rtc cstep i i'.
Proof.
 intros S i u H; remember (TApp (TMuS S) i) as t eqn:E; revert S i E.
 induction H; intros; subst; [exists S,i; repeat split; apply rtc_refl|].
 destruct (cstep_musapp_inv_luna _ _ _ H) as [S1 [i1 [-> [HS Hi]]]].
 destruct (IHrtc S1 i1 eq_refl) as [S2 [i2 [-> [HS2 Hi2]]]].
 exists S2,i2; repeat split; eauto using rtc_step.
Qed.
Lemma cjoin_musapp_inv_luna : forall S1 S2 i1 i2,
  cjoin (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
  cjoin S1 S2 /\ cjoin i1 i2.
Proof.
 intros S1 S2 i1 i2 [w [H1 H2]].
 destruct (rtc_cstep_musapp_inv_luna _ _ _ H1) as [S1' [i1' [Hw1 [HS1 Hi1]]]].
 rewrite Hw1 in H2.
 destruct (rtc_cstep_musapp_inv_luna _ _ _ H2) as [S2' [i2' [Hw2 [HS2 Hi2]]]].
 inversion Hw2; subst S2' i2'. repeat split; unfold cjoin; eauto.
Qed.
Print Assumptions cjoin_musapp_inv_luna.
