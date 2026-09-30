(* GLM worker 1 — stable-representation simulation CONSUMER, part: the       *)
(* complete SORT analogue of _glm_mueq_sim_close_rep.v, built parametrically *)
(* from its mueq_cstep_sim_glm premise (which remains a binder).             *)
(*                                                                           *)
(*   sort_rep t j := cjoin t (TSort j)                                       *)
(*                                                                           *)
(* Pipeline:                                                                 *)
(*                                                                           *)
(*   1. transport mueq t u across the rtc cstep witnessing sort_rep t j      *)
(*      (mueq_rtc_cstep_sim_glm from _glm_mueq_sim_close_rep);               *)
(*   2. stable cstep inversion forces the left common reduct to TSort j      *)
(*      (rtc_cstep_sort_inv_glm: the sort level is preserved by cstep);      *)
(*   3. mueq inversion forces the transported right reduct to exactly        *)
(*      TSort j (mueq cannot change a sort level: me_sort is reflexive at    *)
(*      a single level and no other mueq class has a sort head);             *)
(*   4. therefore mueq_sort_rep_sim_from_cstep_sim_glm;                      *)
(*   5. qlink and qconv transport of sort_rep;                               *)
(*   6. conv B (TSort j) -> conv (subst a k B) (TSort j), combining           *)
(*      conv_qconv_glm, the qconv transport, cjoin_subst_sort_glm and        *)
(*      cjoin_conv.                                                          *)
(*                                                                           *)
(* No Axiom / Conjecture / Admitted; no dependence on any active full        *)
(* simulation file: the simulation premise stays quantified.                 *)

Require Import Progress.
Require Import _tmp_epstep
               _work_mixed_closure _work_cjoin _work_cstep_invariants
               _luna_mueq _luna_mueq_equiv
               _glm_qconv_def
               _glm_mueq_sim_close_rep
               _glm_cjoin_subst_main
               _glm_qconv_main
               _glm_injectivity_close_rep.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  1. The sort representation                                                *)
(* ========================================================================== *)

Definition sort_rep (t : term) (j : nat) : Prop := cjoin t (TSort j).

(* ========================================================================== *)
(*  2. Stable cstep inversion: sorts are cstep-normal, at the same level       *)
(* ========================================================================== *)

(* A sort never steps: any reduct of TSort j is TSort j again — exactly the  *)
(* level equality the pipeline needs (rtc_cstep_sort_id in                    *)
(* _work_cstep_invariants).                                                  *)
Lemma rtc_cstep_sort_inv_glm : forall j w,
    rtc cstep (TSort j) w -> w = TSort j.
Proof. exact rtc_cstep_sort_id. Qed.

(* Consequently the common reduct witnessing sort_rep t j is TSort j, so     *)
(* sort_rep t j collapses to rtc cstep t (TSort j).                          *)
Lemma cjoin_sort_inv_glm : forall t j,
    sort_rep t j -> rtc cstep t (TSort j).
Proof.
  intros t j Hrep. unfold sort_rep in Hrep.
  destruct Hrep as [w [Ht Hs]].
  rewrite (rtc_cstep_sort_inv_glm j w Hs) in Ht. exact Ht.
Qed.

(* ========================================================================== *)
(*  3. mueq inversion: mueq cannot change a sort level                         *)
(* ========================================================================== *)

(* mueq is shape-directed: me_sort is the only class with a sort head and it *)
(* is reflexive at a single level, so a TSort j on the left forces TSort j   *)
(* on the right — no level change is possible.                               *)
Lemma mueq_sort_shape_inv_glm : forall j x,
    mueq (TSort j) x -> x = TSort j.
Proof.
  intros j x H. inversion H; subst. reflexivity.
Qed.

(* ========================================================================== *)
(*  4. Representation transport across one mueq link (the honest consumer)    *)
(* ========================================================================== *)

(*   sort_rep t j  =>  rtc cstep t (TSort j)            (stable inversion)   *)
(*   mueq t u + rtc cstep t (TSort j)                                        *)
(*                  =>  rtc cstep u w', mueq (TSort j) w'   (rtc transport)  *)
(*   mueq (TSort j) w'  =>  w' = TSort j                (mueq inversion)     *)
(*   sort_rep u j at the witness w' = TSort j.                               *)
Theorem mueq_sort_rep_sim_from_cstep_sim_glm :
    mueq_cstep_sim_glm ->
    forall t u j, mueq t u -> sort_rep t j -> sort_rep u j.
Proof.
  intros SIM t u j Hm Hrep. unfold sort_rep.
  pose proof (cjoin_sort_inv_glm t j Hrep) as Ht.
  destruct (mueq_rtc_cstep_sim_glm SIM t (TSort j) Ht u Hm)
    as [w' [Huw Hmw]].
  rewrite (mueq_sort_shape_inv_glm j w' Hmw) in Huw.
  exists (TSort j). split; [exact Huw | apply rtc_refl].
Qed.

(* The same consumer from the narrow pstep / epstep premises.                *)
Theorem mueq_sort_rep_sim_from_narrow_glm :
    mueq_pstep_sim_glm -> mueq_epstep_sim_glm ->
    forall t u j, mueq t u -> sort_rep t j -> sort_rep u j.
Proof.
  intros Hp He.
  apply mueq_sort_rep_sim_from_cstep_sim_glm.
  apply mueq_cstep_sim_glm_from_narrow; assumption.
Qed.

(* ========================================================================== *)
(*  5. qlink and qconv transport of sort_rep                                  *)
(* ========================================================================== *)

Lemma qlink_sort_rep_sim_glm : mueq_cstep_sim_glm ->
    forall t u j, qlink t u -> sort_rep t j -> sort_rep u j.
Proof.
  intros SIM t u j H Hrep. destruct H as [Hcj | Hm].
  - (* cjoin link: cjoin u t composes with the representation.              *)
    unfold sort_rep in *.
    eapply cjoin_trans; [apply cjoin_sym; exact Hcj | exact Hrep].
  - (* mueq link: the one-step consumer.                                    *)
    exact (mueq_sort_rep_sim_from_cstep_sim_glm SIM t u j Hm Hrep).
Qed.

Lemma qconv_sort_rep_sim_glm : mueq_cstep_sim_glm ->
    forall t u, qconv t u -> forall j, sort_rep t j -> sort_rep u j.
Proof.
  intros SIM t u H.
  induction H as [x | x y z Hxy Hyz IH]; intros j Hrep.
  - exact Hrep.
  - exact (IH j (qlink_sort_rep_sim_glm SIM x y j Hxy Hrep)).
Qed.

(* ========================================================================== *)
(*  6. The sort-target substitution theorem                                   *)
(* ========================================================================== *)

(* conv B (TSort j) routes into the quotient world (conv_qconv_glm), is      *)
(* read backwards from the sort (qconv_sym) carrying the sort representation *)
(* (cjoin_refl (TSort j)) to B, the representation is substituted            *)
(* (cjoin_subst_sort_glm), and cjoin_conv lands back in conv.               *)
Theorem conv_subst_sort_target_from_cstep_sim_glm :
    mueq_cstep_sim_glm ->
    forall B j, conv B (TSort j) ->
    forall a k, conv (subst a k B) (TSort j).
Proof.
  intros SIM B j Hconv a k.
  assert (Hrep : sort_rep B j).
  { apply (qconv_sort_rep_sim_glm SIM (TSort j) B).
    - apply qconv_sym. apply conv_qconv_glm. exact Hconv.
    - apply cjoin_refl. }
  pose proof (cjoin_subst_sort_glm B j Hrep a k) as Hsub.
  apply cjoin_conv. exact Hsub.
Qed.

(* ========================================================================== *)
(*  7. Closedness certificates                                                *)
(* ========================================================================== *)

Print Assumptions mueq_sort_rep_sim_from_cstep_sim_glm.
Print Assumptions mueq_sort_rep_sim_from_narrow_glm.
Print Assumptions qconv_sort_rep_sim_glm.
Print Assumptions conv_subst_sort_target_from_cstep_sim_glm.
