(* GLM worker 1 — mueq lift-descent bundle, part 3: signature checks.        *)
(* Verifies the exact interface requested for the root eta simulation and    *)
(* re-checks closedness of the two headline theorems.                        *)

Require Import Progress.
Require Import _luna_mueq.
Require Import _glm_mueq_lift_descent_shape _glm_mueq_lift_descent_main.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* The requested interface, exactly: *)
Check mueq_lift1_descent_glm :
  conv_muapp_lift1_descent_glm ->
  forall f g, mueq (lift 1 0 f) g ->
    exists g0, g = lift 1 0 g0 /\ mueq f g0.

(* The isolated conversion-level premise (theorem binder): *)
Check conv_muapp_lift1_descent_glm : Prop.

(* Full-offset variants and the mubeq/list descent needed for TCase: *)
Check mueq_lift_descent_k_glm : conv_muapp_lift1_descent_glm ->
    forall k f g, mueq (lift 1 k f) g ->
      exists g0, g = lift 1 k g0 /\ mueq f g0.
Check mueq_lift1_descent_sym_glm : conv_muapp_lift1_descent_glm ->
    forall f g, mueq f (lift 1 0 g) ->
      exists f0, f = lift 1 0 f0 /\ mueq f0 g.
Check mubeq_lift_descent_k_glm : conv_muapp_lift1_descent_glm ->
    forall k bs bs', mubeq (lift_branches k bs) bs' ->
      exists bs0, bs' = lift_branches k bs0 /\ mubeq bs bs0.
Check mubeq_lift1_descent_map_glm : conv_muapp_lift1_descent_glm ->
    forall bs bs',
      mubeq (map (fun '(c, b) => (lift 1 0 c, lift 1 1 b)) bs) bs' ->
      exists bs0,
        bs' = map (fun '(c, b) => (lift 1 0 c, lift 1 1 b)) bs0 /\
        mubeq bs bs0.
Check mubeq_lift_descent_of_mueq_glm.

Print Assumptions mueq_lift1_descent_glm.
Print Assumptions mubeq_lift1_descent_map_glm.
