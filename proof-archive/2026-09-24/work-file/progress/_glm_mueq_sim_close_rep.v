(* GLM worker 3 — stable-representation simulation CONSUMER, part: the       *)
(* complete conditional consumer for the honest component-changing interfaces *)
(* mueq_enumt_sim_components / mueq_pi_sim_components of                      *)
(* _glm_injectivity_close_rep.v, built parametrically from one-step           *)
(* reduction-vs-mueq simulation premises (which remain binders).              *)
(*                                                                           *)
(* Narrow premises (pstep / epstep, and their combined cstep form):          *)
(*                                                                           *)
(*   mueq t u -> pstep  t t' -> exists u', rtc cstep u u' /\ mueq t' u'      *)
(*   mueq t u -> epstep t t' -> exists u', rtc cstep u u' /\ mueq t' u'      *)
(*   mueq t u -> cstep  t t' -> exists u', rtc cstep u u' /\ mueq t' u'      *)
(*                                                                           *)
(* From the cstep premise:                                                   *)
(*                                                                           *)
(*   1. transport across rtc cstep by induction, accumulating rtc;           *)
(*   2. mueq t u + enumt_rep t E = cjoin t (TEnumT E) yields E' with         *)
(*      enumt_rep u E' and qconv E E';                                       *)
(*   3. the analogous Pi representation transport with qconv-related         *)
(*      domain/codomain.                                                     *)
(*                                                                           *)
(* The final theorems exactly inhabit the interface definitions:             *)
(*                                                                           *)
(*   mueq_enumt_sim_components_from_cstep_sim_glm                            *)
(*   mueq_pi_sim_components_from_cstep_sim_glm                               *)
(*                                                                           *)
(* Stable cstep endpoint inversions (rtc_cstep_enumt_inv, rtc_cstep_pi_inv), *)
(* the mueq inversions (_glm_mueq_inv), the cjoin endpoint cancellations     *)
(* (cjoin_enumt_inv_glm, cjoin_pi_inv) and qconv algebra close everything.   *)
(* No Axiom / Conjecture / Admitted; no dependence on any active             *)
(* _glm_mueq_sim* / _glm_mueq_epstep_sim* file.                              *)

Require Import Progress.
Require Import _tmp_epstep
               _work_mixed_closure _work_cjoin _work_cstep_invariants
               _luna_mueq _luna_mueq_equiv
               _glm_qconv_def
               _glm_mueq_inv
               _glm_injectivity_close_rep.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  1. The one-step reduction-vs-mueq simulation premises (binders)           *)
(* ========================================================================== *)

Definition mueq_pstep_sim_glm : Prop :=
  forall t u t', mueq t u -> pstep t t' ->
    exists u', rtc cstep u u' /\ mueq t' u'.

Definition mueq_epstep_sim_glm : Prop :=
  forall t u t', mueq t u -> epstep t t' ->
    exists u', rtc cstep u u' /\ mueq t' u'.

Definition mueq_cstep_sim_glm : Prop :=
  forall t u t', mueq t u -> cstep t t' ->
    exists u', rtc cstep u u' /\ mueq t' u'.

(* The cstep premise is exactly the two narrow premises combined (cstep      *)
(* inverts into its rtc pstep half and its rtc epstep half; each narrow      *)
(* premise transports across its whole rtc chain, accumulating rtc cstep).   *)
Lemma mueq_rtc_pstep_sim_glm : mueq_pstep_sim_glm ->
    forall t t', rtc pstep t t' -> forall u, mueq t u ->
      exists u', rtc cstep u u' /\ mueq t' u'.
Proof.
  intros SIM t t' Hrtc.
  induction Hrtc as [x | x y z Hxy Hyz IH]; intros u Hm.
  - exists u. split; [apply rtc_refl | exact Hm].
  - destruct (SIM x u y Hm Hxy) as [u1 [Huu1 Hm1]].
    destruct (IH u1 Hm1) as [u2 [Hu1u2 Hm2]].
    exists u2. split; [eapply rtc_trans; eassumption | exact Hm2].
Qed.

Lemma mueq_rtc_epstep_sim_glm : mueq_epstep_sim_glm ->
    forall t t', rtc epstep t t' -> forall u, mueq t u ->
      exists u', rtc cstep u u' /\ mueq t' u'.
Proof.
  intros SIM t t' Hrtc.
  induction Hrtc as [x | x y z Hxy Hyz IH]; intros u Hm.
  - exists u. split; [apply rtc_refl | exact Hm].
  - destruct (SIM x u y Hm Hxy) as [u1 [Huu1 Hm1]].
    destruct (IH u1 Hm1) as [u2 [Hu1u2 Hm2]].
    exists u2. split; [eapply rtc_trans; eassumption | exact Hm2].
Qed.

Lemma mueq_cstep_sim_glm_from_narrow :
    mueq_pstep_sim_glm -> mueq_epstep_sim_glm -> mueq_cstep_sim_glm.
Proof.
  intros Hp He t u t' Hm Hc. destruct Hc.
  - exact (mueq_rtc_pstep_sim_glm Hp _ _ H u Hm).
  - exact (mueq_rtc_epstep_sim_glm He _ _ H u Hm).
Qed.

(* ========================================================================== *)
(*  2. Transport across rtc cstep, accumulating rtc                           *)
(* ========================================================================== *)

Lemma mueq_rtc_cstep_sim_glm : mueq_cstep_sim_glm ->
    forall t t', rtc cstep t t' -> forall u, mueq t u ->
      exists u', rtc cstep u u' /\ mueq t' u'.
Proof.
  intros SIM t t' Hrtc.
  induction Hrtc as [x | x y z Hxy Hyz IH]; intros u Hm.
  - exists u. split; [apply rtc_refl | exact Hm].
  - destruct (SIM x u y Hm Hxy) as [u1 [Huu1 Hm1]].
    destruct (IH u1 Hm1) as [u2 [Hu1u2 Hm2]].
    exists u2. split; [eapply rtc_trans; eassumption | exact Hm2].
Qed.

(* ========================================================================== *)
(*  3. Representation toolkit: qconv from reduction, mueq shape/component     *)
(*     inversions, cjoin endpoint alignment                                   *)
(* ========================================================================== *)

(* Reduction re-enters the qconv world: a cstep is joinable in one step.     *)
Lemma rtc_cstep_qconv_glm : forall t u, rtc cstep t u -> qconv t u.
Proof.
  intros t u H.
  induction H as [x | x y z Hxy Hyz IH].
  - apply qconv_refl.
  - eapply qconv_trans.
    + apply cjoin_qconv. exists y. split;
        [apply rtc_one; exact Hxy | apply rtc_refl].
    + exact IH.
Qed.

(* Both-sides mueq component inversions (via _glm_mueq_inv).                 *)
Lemma mueq_enumt_comp_qconv_glm : forall E1 E2,
    mueq (TEnumT E1) (TEnumT E2) -> qconv E1 E2.
Proof.
  intros E1 E2 H. apply mueq_qconv. apply mueq_enumt_inv_glm. exact H.
Qed.

Lemma mueq_pi_comp_qconv_glm : forall A1 B1 A2 B2,
    mueq (TPi A1 B1) (TPi A2 B2) -> qconv A1 A2 /\ qconv B1 B2.
Proof.
  intros A1 B1 A2 B2 H.
  destruct (mueq_pi_inv_glm A1 A2 B1 B2 H) as [HA HB].
  split; apply mueq_qconv; assumption.
Qed.

(* Shape-directed mueq inversions: mueq cannot change a stable syntactic     *)
(* head (mueq is shape-directed; the opaque me_muapp class only arises at    *)
(* applications), so a TEnumT/TPi on the left forces the same head on the    *)
(* right and relates the components.                                         *)
Lemma mueq_enumt_shape_inv_glm : forall E x,
    mueq (TEnumT E) x -> exists E', x = TEnumT E' /\ mueq E E'.
Proof.
  intros E x H. inversion H; subst.
  eexists. split; [reflexivity | eassumption].
Qed.

Lemma mueq_pi_shape_inv_glm : forall A B x,
    mueq (TPi A B) x ->
    exists A' B', x = TPi A' B' /\ mueq A A' /\ mueq B B'.
Proof.
  intros A B x H. inversion H; subst.
  eexists; eexists. split; [reflexivity | split; assumption].
Qed.

(* cjoin endpoint alignment: when two stable endpoints join, the components  *)
(* join (cjoin_enumt_inv_glm / cjoin_pi_inv) and the representation can be   *)
(* re-anchored at either endpoint with an unchanged carrier.                 *)
Lemma enumt_rep_align_glm : forall E1 E2 t,
    cjoin (TEnumT E1) (TEnumT E2) -> enumt_rep t E1 -> enumt_rep t E2.
Proof.
  intros E1 E2 t Hc Hrep. unfold enumt_rep in *.
  eapply cjoin_trans; [exact Hrep | exact Hc].
Qed.

Lemma enumt_rep_align_qconv_glm : forall E1 E2,
    cjoin (TEnumT E1) (TEnumT E2) -> qconv E1 E2.
Proof.
  intros E1 E2 H. apply cjoin_qconv. apply cjoin_enumt_inv_glm. exact H.
Qed.

Lemma pi_rep_align_glm : forall A1 B1 A2 B2 t,
    cjoin (TPi A1 B1) (TPi A2 B2) -> pi_rep t A1 B1 -> pi_rep t A2 B2.
Proof.
  intros A1 B1 A2 B2 t Hc Hrep. unfold pi_rep in *.
  eapply cjoin_trans; [exact Hrep | exact Hc].
Qed.

Lemma pi_rep_align_qconv_glm : forall A1 B1 A2 B2,
    cjoin (TPi A1 B1) (TPi A2 B2) -> qconv A1 A2 /\ qconv B1 B2.
Proof.
  intros A1 B1 A2 B2 H.
  destruct (cjoin_pi_inv A1 B1 A2 B2 H) as [HA HB].
  split; apply cjoin_qconv; assumption.
Qed.

(* ========================================================================== *)
(*  4. Representation transport across one mueq link (the honest consumers)   *)
(* ========================================================================== *)

(* Step 2 of the plan: from mueq t u and cjoin t (TEnumT E), extract E'      *)
(* with cjoin u (TEnumT E') and qconv E E'.                                  *)
(*                                                                           *)
(*   cjoin t (TEnumT E)  =>  w with rtc cstep t w, rtc cstep (TEnumT E) w    *)
(*   rtc cstep (TEnumT E) w  =>  w = TEnumT Ew, rtc cstep E Ew   (stable)    *)
(*   rtc cstep t w /\ mueq t u  =>  rtc cstep u w', mueq w w'    (transport) *)
(*   mueq (TEnumT Ew) w'  =>  w' = TEnumT Ew', mueq Ew Ew'       (shape)     *)
(*   cjoin u (TEnumT Ew')  at witness w';  qconv E Ew' by qconv_trans.       *)
Lemma enumt_rep_mueq_transport_glm : mueq_cstep_sim_glm ->
    forall t u E, mueq t u -> enumt_rep t E ->
      exists E', enumt_rep u E' /\ qconv E E'.
Proof.
  intros SIM t u E Hm Hrep. unfold enumt_rep in Hrep.
  destruct Hrep as [w [Htw Hwen]].
  destruct (mueq_rtc_cstep_sim_glm SIM t w Htw u Hm) as [w' [Huw Hmw]].
  destruct (rtc_cstep_enumt_inv _ _ Hwen) as [Ew [Hw HEEw]]. subst w.
  destruct (mueq_enumt_shape_inv_glm _ _ Hmw) as [Ew' [Hw' HmEw]]. subst w'.
  exists Ew'. split.
  - exists (TEnumT Ew'). split; [exact Huw | apply rtc_refl].
  - eapply qconv_trans.
    + apply rtc_cstep_qconv_glm. exact HEEw.
    + apply mueq_qconv. exact HmEw.
Qed.

(* Step 3 of the plan: the analogous Pi representation transport with        *)
(* qconv-related domain and codomain.                                        *)
Lemma pi_rep_mueq_transport_glm : mueq_cstep_sim_glm ->
    forall t u A B, mueq t u -> pi_rep t A B ->
      exists A' B', pi_rep u A' B' /\ qconv A A' /\ qconv B B'.
Proof.
  intros SIM t u A B Hm Hrep. unfold pi_rep in Hrep.
  destruct Hrep as [w [Htw Hwpi]].
  destruct (mueq_rtc_cstep_sim_glm SIM t w Htw u Hm) as [w' [Huw Hmw]].
  destruct (rtc_cstep_pi_inv _ _ _ Hwpi) as [Aw [Bw [Hw [HAAw HBBw]]]]. subst w.
  destruct (mueq_pi_shape_inv_glm _ _ _ Hmw) as [Aw' [Bw' [Hw' [HmAw HmBw]]]].
  subst w'.
  exists Aw', Bw'. split.
  - exists (TPi Aw' Bw'). split; [exact Huw | apply rtc_refl].
  - split.
    + eapply qconv_trans.
      * apply rtc_cstep_qconv_glm. exact HAAw.
      * apply mueq_qconv. exact HmAw.
    + eapply qconv_trans.
      * apply rtc_cstep_qconv_glm. exact HBBw.
      * apply mueq_qconv. exact HmBw.
Qed.

(* ========================================================================== *)
(*  5. The required interface inhabitants                                     *)
(* ========================================================================== *)

Theorem mueq_enumt_sim_components_from_cstep_sim_glm :
    mueq_cstep_sim_glm -> mueq_enumt_sim_components.
Proof. exact enumt_rep_mueq_transport_glm. Qed.

Theorem mueq_pi_sim_components_from_cstep_sim_glm :
    mueq_cstep_sim_glm -> mueq_pi_sim_components.
Proof. exact pi_rep_mueq_transport_glm. Qed.

(* The same consumers from the narrow pstep / epstep premises.               *)
Theorem mueq_enumt_sim_components_from_narrow_sim_glm :
    mueq_pstep_sim_glm -> mueq_epstep_sim_glm -> mueq_enumt_sim_components.
Proof.
  intros Hp He.
  apply mueq_enumt_sim_components_from_cstep_sim_glm.
  apply mueq_cstep_sim_glm_from_narrow; assumption.
Qed.

Theorem mueq_pi_sim_components_from_narrow_sim_glm :
    mueq_pstep_sim_glm -> mueq_epstep_sim_glm -> mueq_pi_sim_components.
Proof.
  intros Hp He.
  apply mueq_pi_sim_components_from_cstep_sim_glm.
  apply mueq_cstep_sim_glm_from_narrow; assumption.
Qed.

(* ========================================================================== *)
(*  6. Full qconv-chain consumers (cjoin links for free, mueq links via the   *)
(*     transport above), accumulating the component qconv with qconv_trans    *)
(* ========================================================================== *)

Lemma enumt_rep_qconv_transport_glm : mueq_cstep_sim_glm ->
    forall t u, qconv t u -> forall E, enumt_rep t E ->
      exists E', enumt_rep u E' /\ qconv E E'.
Proof.
  intros SIM t u H.
  induction H as [x | x y z Hxy Hyz IH]; intros E Hrep.
  - exists E. split; [exact Hrep | apply qconv_refl].
  - destruct Hxy as [Hcj | Hm].
    + (* cjoin link: cjoin u t composes with the representation; component   *)
      (* unchanged.                                                          *)
      destruct (IH E (cjoin_trans y x (TEnumT E) (cjoin_sym x y Hcj) Hrep))
        as [E' [Hrep' HqE]].
      exists E'. split; [exact Hrep' | exact HqE].
    + (* mueq link: the one-step consumer, then the chain hypothesis.        *)
      destruct (enumt_rep_mueq_transport_glm SIM x y E Hm Hrep)
        as [E1 [Hrep1 HqE1]].
      destruct (IH E1 Hrep1) as [E2 [Hrep2 HqE2]].
      exists E2. split; [exact Hrep2 | eapply qconv_trans; eassumption].
Qed.

Lemma pi_rep_qconv_transport_glm : mueq_cstep_sim_glm ->
    forall t u, qconv t u -> forall A B, pi_rep t A B ->
      exists A' B', pi_rep u A' B' /\ qconv A A' /\ qconv B B'.
Proof.
  intros SIM t u H.
  induction H as [x | x y z Hxy Hyz IH]; intros A B Hrep.
  - exists A, B. split; [exact Hrep | split; apply qconv_refl].
  - destruct Hxy as [Hcj | Hm].
    + destruct (IH A B (cjoin_trans y x (TPi A B) (cjoin_sym x y Hcj) Hrep))
        as [A' [B' [Hrep' [HqA HqB]]]].
      exists A', B'. split; [exact Hrep' | split; assumption].
    + destruct (pi_rep_mueq_transport_glm SIM x y A B Hm Hrep)
        as [A1 [B1 [Hrep1 [HqA1 HqB1]]]].
      destruct (IH A1 B1 Hrep1) as [A2 [B2 [Hrep2 [HqA2 HqB2]]]].
      exists A2, B2. split; [exact Hrep2 | split].
      * eapply qconv_trans; eassumption.
      * eapply qconv_trans; eassumption.
Qed.

(* ========================================================================== *)
(*  7. Closedness certificates                                                *)
(* ========================================================================== *)

Print Assumptions mueq_enumt_sim_components_from_cstep_sim_glm.
Print Assumptions mueq_pi_sim_components_from_cstep_sim_glm.
Print Assumptions mueq_enumt_sim_components_from_narrow_sim_glm.
Print Assumptions mueq_pi_sim_components_from_narrow_sim_glm.
Print Assumptions enumt_rep_qconv_transport_glm.
Print Assumptions pi_rep_qconv_transport_glm.
