(* ========================================================================== *)
(*  _glm_phi_erase_reflect_close_reflect.v — GLM worker 2: the CONDITIONAL    *)
(*  closing layer built from two ONE-STEP erasure reflection interfaces.      *)
(*                                                                            *)
(*  The interfaces are theorem binders (definitions used as premises, never   *)
(*  axioms):                                                                  *)
(*                                                                            *)
(*    erase_pstep_reflect  := forall t u, pstep (phi_erase t) u ->            *)
(*                              exists t', pstep t t' /\ phi_erase t' = u.    *)
(*    erase_epstep_reflect := forall t u, epstep (phi_erase t) u ->           *)
(*                              exists t', epstep t t' /\ phi_erase t' = u.   *)
(*                                                                            *)
(*  Contents (every step a small named lemma):                                *)
(*    1. rtc pstep and rtc epstep reflection — the generic transport          *)
(*       rtc_erase_reflect_gen carries a PREIMAGE TERM at every step.         *)
(*    2. cstep and rtc cstep reflection.                                      *)
(*    3. Stable sort reflection:                                              *)
(*          stable_sort_erase_reflect_glm :                                   *)
(*            erase_pstep_reflect -> erase_epstep_reflect ->                  *)
(*            forall B j, rtc cstep (phi_erase B) (TSort j) ->                *)
(*              conv B (TSort j).                                             *)
(*       Stability of sorts (rtc_cstep_sort_id of _work_cstep_invariants)     *)
(*       pins the reflected preimage to a syntactic sort via the head-        *)
(*       injectivity of phi_erase; rtc_cstep_conv then re-enters conv.        *)
(*                                                                            *)
(*  No Axiom / Conjecture / Admitted / admit / Abort; no Progress.v           *)
(*  conjecture; no active reflection/simulation imports.                      *)
(* ========================================================================== *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  0. The one-step erasure reflection interfaces (binders).                  *)
(* ========================================================================== *)

Definition erase_pstep_reflect : Prop :=
  forall t u, pstep (phi_erase t) u ->
    exists t', pstep t t' /\ phi_erase t' = u.

Definition erase_epstep_reflect : Prop :=
  forall t u, epstep (phi_erase t) u ->
    exists t', epstep t t' /\ phi_erase t' = u.

(* ========================================================================== *)
(*  1. Reflection along rtc, carrying a preimage term at every step.          *)
(* ========================================================================== *)

(* Generic transport: a one-step reflection on R lifts to the reflexive-
   transitive closure.  The preimage term is threaded through the whole
   induction: each rtc_step consumes one instance of the one-step binder. *)
Lemma rtc_erase_reflect_gen :
  forall (R : term -> term -> Prop),
    (forall t u, R (phi_erase t) u ->
       exists t', R t t' /\ phi_erase t' = u) ->
    forall t u, rtc R (phi_erase t) u ->
    exists t', rtc R t t' /\ phi_erase t' = u.
Proof.
  intros R Hone t u H.
  remember (phi_erase t) as s eqn:Hs. revert t Hs.
  induction H as [x | x y z Hxy Hrest IH]; intros t Hs.
  - (* rtc_refl : the preimage of the erased source is the source itself *)
    exists t. split.
    + apply rtc_refl.
    + symmetry. exact Hs.
  - (* rtc_step : lift the first step at the preimage, then induct *)
    assert (Hxy' : R (phi_erase t) y) by (rewrite <- Hs; exact Hxy).
    destruct (Hone t y Hxy') as [t1 [Ht1 He1]].
    destruct (IH t1 (eq_sym He1)) as [t2 [Ht2 He2]].
    exists t2. split.
    + eapply rtc_step; [exact Ht1 | exact Ht2].
    + exact He2.
Qed.

Lemma rtc_pstep_erase_reflect_glm :
  erase_pstep_reflect ->
  forall t u, rtc pstep (phi_erase t) u ->
  exists t', rtc pstep t t' /\ phi_erase t' = u.
Proof. intros Hp. eapply rtc_erase_reflect_gen; exact Hp. Qed.

Lemma rtc_epstep_erase_reflect_glm :
  erase_epstep_reflect ->
  forall t u, rtc epstep (phi_erase t) u ->
  exists t', rtc epstep t t' /\ phi_erase t' = u.
Proof. intros He. eapply rtc_erase_reflect_gen; exact He. Qed.

(* ========================================================================== *)
(*  2. cstep and rtc cstep reflection.                                        *)
(* ========================================================================== *)

Lemma cstep_erase_reflect_one_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall t u, cstep (phi_erase t) u ->
  exists t', cstep t t' /\ phi_erase t' = u.
Proof.
  intros Hp He t u H. inversion H; subst.
  - destruct (rtc_pstep_erase_reflect_glm Hp _ _ H0) as [t' [Ht' He']].
    exists t'. split; [apply cs_core; exact Ht' | exact He'].
  - destruct (rtc_epstep_erase_reflect_glm He _ _ H0) as [t' [Ht' He']].
    exists t'. split; [apply cs_eta; exact Ht' | exact He'].
Qed.

Lemma rtc_cstep_erase_reflect_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall t u, rtc cstep (phi_erase t) u ->
  exists t', rtc cstep t t' /\ phi_erase t' = u.
Proof.
  intros Hp He. eapply rtc_erase_reflect_gen.
  intros t0 u0 H0. eapply cstep_erase_reflect_one_glm; eassumption.
Qed.

(* ========================================================================== *)
(*  3. Stable sort reflection.                                                *)
(* ========================================================================== *)

(* phi_erase preserves every head constructor except TMuS, whose erasure is
   TMuS TUnit; hence a term erasing to a syntactic sort IS that sort. *)
Lemma phi_erase_sort_inv_glm : forall t j, phi_erase t = TSort j -> t = TSort j.
Proof.
  intros t j H. destruct t; simpl in H; try discriminate; congruence.
Qed.

(* The stable sort reflection: whenever the erasure of B reduces (rtc cstep)
   to the stable endpoint TSort j, B itself converts to TSort j. *)
Lemma stable_sort_erase_reflect_glm :
  erase_pstep_reflect -> erase_epstep_reflect ->
  forall B j, rtc cstep (phi_erase B) (TSort j) -> conv B (TSort j).
Proof.
  intros Hp He B j H.
  destruct (rtc_cstep_erase_reflect_glm Hp He _ _ H) as [B' [HB' He']].
  assert (HB'2 : B' = TSort j) by (eapply phi_erase_sort_inv_glm; exact He').
  subst B'. apply rtc_cstep_conv; exact HB'.
Qed.

Print Assumptions stable_sort_erase_reflect_glm.
Print Assumptions rtc_cstep_erase_reflect_glm.
