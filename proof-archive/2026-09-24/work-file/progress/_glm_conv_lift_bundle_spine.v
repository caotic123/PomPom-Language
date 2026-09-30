(* GLM worker 1 — conv-lift bundle, part 3: closed corollary — spine_phi    *)
(* survives de Bruijn lifting (worker-2 section instantiated with part 1).  *)

Require Import TypeRules Progress.
Require Import _glm_neutral_lift _glm_desc_against_lift _glm_spine_phi_lift
               _glm_conv_lift_bundle_eval.

Theorem spine_phi_lift_glm_closed :
  forall Sf i Phi Psi, spine_phi Sf i Phi Psi -> forall d k,
    spine_phi (lift d k Sf) (lift d k i) (lift d k Phi) (lift d k Psi).
Proof.
  exact (spine_phi_lift_glm eval_lift_compatible_glm_proved).
Qed.

Check spine_phi_lift_glm_closed :
  forall Sf i Phi Psi, spine_phi Sf i Phi Psi -> forall d k,
    spine_phi (lift d k Sf) (lift d k i) (lift d k Phi) (lift d k Psi).
