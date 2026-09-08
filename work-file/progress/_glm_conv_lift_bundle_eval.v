(* GLM worker 1 — conv-lift bundle, part 1: weak-head evaluation commutes   *)
(* with de Bruijn lifting (from step_lift_glm), and the resulting           *)
(* instantiation of eval_lift_compatible_glm that closes the worker-2       *)
(* desc_against / spine_phi sections.                                       *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules Progress.
Require Import _glm_step_lift _glm_desc_against_lift.

Theorem eval_lift_glm : forall t u, eval t u -> forall d k,
    eval (lift d k t) (lift d k u).
Proof.
  intros t u H.
  induction H as [t | t u v Hst Htail IH]; intros d kk.
  - (* ev_refl *)
    apply ev_refl.
  - (* ev_step *)
    eapply ev_step.
    + apply (step_lift_glm t u Hst d kk).
    + exact (IH d kk).
Qed.

Theorem eval_lift_compatible_glm_proved : eval_lift_compatible_glm.
Proof. exact (fun d k t u H => eval_lift_glm t u H d k). Qed.

Check eval_lift_glm :
  forall t u, eval t u -> forall d k, eval (lift d k t) (lift d k u).
Check eval_lift_compatible_glm_proved : eval_lift_compatible_glm.
