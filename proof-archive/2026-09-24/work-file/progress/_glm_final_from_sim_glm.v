(* GLM worker 1 — _glm_final_from_sim_glm.v: the final COMPLETE conditional  *)
(* bridge from the two narrow simulation interfaces                          *)
(*                                                                           *)
(*   mueq_pstep_sim_glm  : mueq t u -> pstep  t t' -> exists u',             *)
(*                           rtc cstep u u' /\ mueq t' u'                    *)
(*   mueq_epstep_sim_glm : mueq t u -> epstep t t' -> exists u',             *)
(*                           rtc cstep u u' /\ mueq t' u'                    *)
(*                                                                           *)
(* (both defined in _glm_mueq_sim_close_rep.v) to the four closing theorems. *)
(* Hp / He remain theorem binders throughout — nothing is assumed globally.  *)
(*                                                                           *)
(* Pipeline (every step a small named bridge lemma, all premise-carried):    *)
(*                                                                           *)
(*   1. mueq_cstep_sim_glm_from_narrow            (_glm_mueq_sim_close_rep)  *)
(*        Hp -> He -> mueq_cstep_sim_glm                                     *)
(*   2. mueq_enumt_sim_components_from_cstep_sim_glm                         *)
(*      mueq_pi_sim_components_from_cstep_sim_glm (_glm_mueq_sim_close_rep)  *)
(*        mueq_cstep_sim_glm -> the honest component-changing interfaces     *)
(*   3. conv_enumt_inj_from_component_sim_glm                                *)
(*      conv_pi_inj_from_component_sim_glm        (_glm_injectivity_close_   *)
(*                                                 main)                     *)
(*        component sim -> exact conv injectivity at TEnumT / TPi            *)
(*        (conv -> qconv via conv_qconv_glm; representation transport along  *)
(*        the qconv chain accumulating component qconvs; stable-endpoint     *)
(*        cancellation cjoin_enumt_inv_glm / cjoin_pi_inv; back to conv via  *)
(*        qconv_conv)                                                        *)
(*   4. conv_subst_sort_target_from_cstep_sim_glm (_glm_mueq_sim_close_sort) *)
(*        mueq_cstep_sim_glm ->                                              *)
(*          forall B j, conv B (TSort j) -> forall a k,                      *)
(*            conv (subst a k B) (TSort j)                                   *)
(*   5. muapp_sort_from_specialized_compat_glm    (_glm_muapp_sort_          *)
(*                                                 specialized)              *)
(*        with the Pi-codomain compatibility taken from theorem 2's second   *)
(*        component (conv_pi injectivity) and the specialized sort-target    *)
(*        substitution taken from theorem 3.                                 *)
(*                                                                           *)
(* No Axiom / Conjecture / Admitted / admit / Abort; no Progress.v           *)
(* conjectures; no dependency on any active full simulation file.            *)
(* Print Assumptions on all four required theorems reports:                  *)
(*   Closed under the global context.                                        *)
(* ========================================================================== *)

Require Import Progress.
Require Import _tmp_epstep
               _work_mixed_closure _work_cjoin _work_cstep_invariants
               _luna_mueq _luna_mueq_equiv
               _glm_qconv_def _glm_qconv_main
               _glm_injectivity_close_rep _glm_injectivity_close_main
               _glm_mueq_sim_close_rep _glm_mueq_sim_close_sort
               _glm_cjoin_subst_main
               _glm_muapp_sort_close _glm_muapp_sort_specialized.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  Pipeline step 1: the narrow premises combine into the cstep premise.      *)
(* ========================================================================== *)

Lemma cstep_sim_from_narrow_bridge_glm :
    mueq_pstep_sim_glm -> mueq_epstep_sim_glm -> mueq_cstep_sim_glm.
Proof. exact mueq_cstep_sim_glm_from_narrow. Qed.

(* ========================================================================== *)
(*  Required theorem 1: EnumT injectivity of conv, conditionally.             *)
(* ========================================================================== *)

Theorem conv_enumt_inj_from_narrow_sim_glm :
    mueq_pstep_sim_glm -> mueq_epstep_sim_glm ->
    forall E1 E2, conv (TEnumT E1) (TEnumT E2) -> conv E1 E2.
Proof.
  intros Hp He.
  apply conv_enumt_inj_from_component_sim_glm.
  apply mueq_enumt_sim_components_from_cstep_sim_glm.
  apply cstep_sim_from_narrow_bridge_glm; assumption.
Qed.

(* ========================================================================== *)
(*  Required theorem 2: Pi injectivity of conv, conditionally.                *)
(* ========================================================================== *)

Theorem conv_pi_inj_from_narrow_sim_glm :
    mueq_pstep_sim_glm -> mueq_epstep_sim_glm ->
    forall A0 B0 A1 B1,
      conv (TPi A0 B0) (TPi A1 B1) -> conv A0 A1 /\ conv B0 B1.
Proof.
  intros Hp He.
  apply conv_pi_inj_from_component_sim_glm.
  apply mueq_pi_sim_components_from_cstep_sim_glm.
  apply cstep_sim_from_narrow_bridge_glm; assumption.
Qed.

(* ========================================================================== *)
(*  Required theorem 3: sort-target substitution transport, conditionally.    *)
(* ========================================================================== *)

Theorem conv_subst_sort_target_from_narrow_sim_glm :
    mueq_pstep_sim_glm -> mueq_epstep_sim_glm ->
    forall B j, conv B (TSort j) ->
    forall a k, conv (subst a k B) (TSort j).
Proof.
  intros Hp He.
  apply conv_subst_sort_target_from_cstep_sim_glm.
  apply cstep_sim_from_narrow_bridge_glm; assumption.
Qed.

(* ========================================================================== *)
(*  Required theorem 4: muapp weak heads are sorts, conditionally.            *)
(*  The specialized-compatibility consumer's two interfaces are discharged    *)
(*  exactly as prescribed: Pi-codomain compatibility from theorem 2, the      *)
(*  specialized sort-target substitution from theorem 3.                     *)
(* ========================================================================== *)

Theorem muapp_sort_from_narrow_sim_glm :
    mueq_pstep_sim_glm -> mueq_epstep_sim_glm ->
    forall f a T U h,
      check [] (TApp f a) T -> value (TApp f a) ->
      conv T U -> whd U h -> h = HSort.
Proof.
  intros Hp He.
  apply muapp_sort_from_specialized_compat_glm.
  - (* conv_pi_codomain_compatible_glm, from theorem 2's second component *)
    intros A0 B0 A1 B1 Hcv.
    destruct (conv_pi_inj_from_narrow_sim_glm Hp He A0 B0 A1 B1 Hcv)
      as [_ HB].
    exact HB.
  - (* conv_subst_sort_target_compatible_glm, from theorem 3 *)
    intros B j Hcv a k.
    exact (conv_subst_sort_target_from_narrow_sim_glm Hp He B j Hcv a k).
Qed.

(* ========================================================================== *)
(*  Closedness certificates — all must report:                                *)
(*  Closed under the global context                                           *)
(* ========================================================================== *)

Print Assumptions conv_enumt_inj_from_narrow_sim_glm.
Print Assumptions conv_pi_inj_from_narrow_sim_glm.
Print Assumptions conv_subst_sort_target_from_narrow_sim_glm.
Print Assumptions muapp_sort_from_narrow_sim_glm.
