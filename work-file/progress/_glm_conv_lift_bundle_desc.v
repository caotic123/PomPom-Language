(* GLM worker 1 — conv-lift bundle, part 2: closed corollary — desc_against *)
(* survives de Bruijn lifting (worker-2 section instantiated with part 1).  *)

Require Import TypeRules Progress.
Require Import _glm_desc_against_lift _glm_conv_lift_bundle_eval.

Theorem desc_against_lift_glm_closed :
  forall D, desc_against D -> forall d k, desc_against (lift d k D).
Proof.
  exact (desc_against_lift_glm eval_lift_compatible_glm_proved).
Qed.

Check desc_against_lift_glm_closed :
  forall D, desc_against D -> forall d k, desc_against (lift d k D).
