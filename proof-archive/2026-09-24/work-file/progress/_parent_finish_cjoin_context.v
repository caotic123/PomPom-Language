Require Import Progress SignatureLemmas.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules Progress._tmp_epstep Progress._tmp_epstep_subst
  Progress._work_mixed_closure Progress._work_cjoin Progress._work_cstep_invariants
  Progress.MuApplicationSort.

Lemma rtc_map_parent {A B : Type} (R : A -> A -> Prop) (S : B -> B -> Prop)
  (F : A -> B) (HF : forall t u,R t u -> S(F t)(F u)) :
  forall t u,rtc R t u -> rtc S(F t)(F u).
Proof. intros t u H; induction H; eauto using rtc_refl,rtc_step. Qed.

Lemma cstep_map_parent (F:term->term)
 (HP:forall t u,pstep t u->pstep(F t)(F u))
 (HE:forall t u,epstep t u->epstep(F t)(F u)) :
 forall t u,cstep t u->cstep(F t)(F u).
Proof.
 intros t u H; inversion H; subst.
 - apply cs_core. eapply rtc_map_parent; eassumption.
 - apply cs_eta. eapply rtc_map_parent; eassumption.
Qed.

Lemma cjoin_map_parent (F:term->term)
 (HP:forall t u,pstep t u->pstep(F t)(F u))
 (HE:forall t u,epstep t u->epstep(F t)(F u)) :
 forall t u,cjoin t u->cjoin(F t)(F u).
Proof.
 intros t u [w [HT HU]]. exists(F w). split;
 (eapply rtc_map_parent; [apply cstep_map_parent; eassumption | eassumption]).
Qed.

Lemma cjoin_map2_parent (F:term->term->term)
 (HP1:forall a b u,pstep a b->pstep(F a u)(F b u))
 (HP2:forall a b u,pstep a b->pstep(F u a)(F u b))
 (HE1:forall a b u,epstep a b->epstep(F a u)(F b u))
 (HE2:forall a b u,epstep a b->epstep(F u a)(F u b)) :
 forall a a' b b',cjoin a a'->cjoin b b'->cjoin(F a b)(F a' b').
Proof.
 intros a a' b b' HA HB. eapply cjoin_trans.
 - eapply (cjoin_map_parent (fun z=>F z b)); eauto.
 - eapply (cjoin_map_parent (fun z=>F a' z)); eauto.
Qed.

Lemma cjoin_sigma_parent : forall A A' B B',cjoin A A' -> cjoin B B' ->
 cjoin(TSigma A B)(TSigma A' B').
Proof.
 eapply cjoin_map2_parent; intros; constructor;
 eauto using pstep_refl,epstep_refl.
Qed.
Lemma cjoin_app_parent : forall A A' B B',cjoin A A' -> cjoin B B' ->
 cjoin(TApp A B)(TApp A' B').
Proof.
 eapply cjoin_map2_parent; intros; apply ps_app || apply eps_app;
 eauto using pstep_refl,epstep_refl.
Qed.
Lemma cjoin_interp_parent : forall A A' B B',cjoin A A' -> cjoin B B' ->
 cjoin(TInterp A B)(TInterp A' B').
Proof.
 eapply cjoin_map2_parent; intros; apply ps_interp || apply eps_interp;
 eauto using pstep_refl,epstep_refl.
Qed.
Lemma cjoin_enumt_parent : forall E E',cjoin E E'->cjoin(TEnumT E)(TEnumT E').
Proof. eapply cjoin_map_parent; intros; constructor; assumption. Qed.
Lemma cjoin_lift_parent : forall t u,cjoin t u->forall d k,cjoin(lift d k t)(lift d k u).
Proof.
 intros t u H d k. eapply cjoin_map_parent; [| |exact H]; intros.
 - apply pstep_lift; assumption.
 - apply epstep_lift; assumption.
Qed.

Print Assumptions cjoin_sigma_parent.
Print Assumptions cjoin_lift_parent.

Lemma pstep_conse_inv_parent : forall A B u, pstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_conse_inv_parent : forall A B u, rtc pstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TConsE A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_conse_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_conse_inv_parent : forall A B u, epstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_conse_inv_parent : forall A B u, rtc epstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TConsE A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_conse_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_conse_inv_parent : forall A B u, cstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_conse_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_conse_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_conse_inv_parent : forall A B u, rtc cstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TConsE A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_conse_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_conse_inv_parent : forall A1 B1 A2 B2,
    cjoin (TConsE A1 B1) (TConsE A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_conse_inv_parent _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_conse_inv_parent _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.


Print Assumptions cjoin_conse_inv_parent.

Lemma pstep_iprod_inv_parent : forall A B u, pstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_iprod_inv_parent : forall A B u, rtc pstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TIProd A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_iprod_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_iprod_inv_parent : forall A B u, epstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_iprod_inv_parent : forall A B u, rtc epstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TIProd A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_iprod_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_iprod_inv_parent : forall A B u, cstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_iprod_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_iprod_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_iprod_inv_parent : forall A B u, rtc cstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TIProd A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_iprod_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_iprod_inv_parent : forall A1 B1 A2 B2,
    cjoin (TIProd A1 B1) (TIProd A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_iprod_inv_parent _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_iprod_inv_parent _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.


Lemma pstep_ichoice_inv_parent : forall A B u, pstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_ichoice_inv_parent : forall A B u, rtc pstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TIChoice A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_ichoice_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_ichoice_inv_parent : forall A B u, epstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_ichoice_inv_parent : forall A B u, rtc epstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TIChoice A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_ichoice_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_ichoice_inv_parent : forall A B u, cstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_ichoice_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_ichoice_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_ichoice_inv_parent : forall A B u, rtc cstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TIChoice A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_ichoice_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_ichoice_inv_parent : forall A1 B1 A2 B2,
    cjoin (TIChoice A1 B1) (TIChoice A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_ichoice_inv_parent _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_ichoice_inv_parent _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.


Lemma no_cjoin_iprod_ichoice_parent : forall A B E F,
 ~cjoin(TIProd A B)(TIChoice E F).
Proof.
 intros A B E F [w [H1 H2]].
 destruct(rtc_cstep_iprod_inv_parent _ _ _ H1) as [A' [B' [-> _]]].
 destruct(rtc_cstep_ichoice_inv_parent _ _ _ H2) as [E' [F' [HH _]]].
 discriminate.
Qed.
