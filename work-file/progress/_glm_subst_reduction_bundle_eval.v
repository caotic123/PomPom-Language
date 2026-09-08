(* GLM worker 1 — eval_subst_glm: weak-head evaluation commutes with         *)
(* same-substituent substitution, via step_subst_glm.                        *)

Require Import TypeRules Progress.
Require Import _glm_subst_reduction_bundle_step.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Theorem eval_subst_glm : forall t v, eval t v -> forall u k,
    eval (subst u k t) (subst u k v).
Proof.
  intros t v H.
  induction H as [t | t w v Hst Heval IH]; intros u k.
  - (* ev_refl *)
    apply ev_refl.
  - (* ev_step *)
    eapply ev_step.
    + exact (step_subst_glm _ _ Hst u k).
    + exact (IH u k).
Qed.

(* Convenience form matching the shape used by the semantic bundle below.   *)
Definition eval_subst_compatible_glm : Prop :=
  forall (u : term) (k : nat) (t v : term),
    eval t v -> eval (subst u k t) (subst u k v).

Theorem eval_subst_compatible_glm_holds : eval_subst_compatible_glm.
Proof.
  intros u k t v H. exact (eval_subst_glm t v H u k).
Qed.
