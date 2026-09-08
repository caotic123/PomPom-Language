(* GLM worker 3 — conditional closing layer for exact EnumT / Pi conversion  *)
(* injectivity, part 2 (main): the exact conditional theorems.               *)
(*                                                                           *)
(*   conv_enumt_inj_from_component_sim_glm :                                 *)
(*     mueq_enumt_sim_components -> forall E1 E2,                            *)
(*       conv (TEnumT E1) (TEnumT E2) -> conv E1 E2                          *)
(*   conv_pi_inj_from_component_sim_glm :                                    *)
(*     mueq_pi_sim_components -> forall A0 B0 A1 B1,                         *)
(*       conv (TPi A0 B0) (TPi A1 B1) -> conv A0 A1 /\ conv B0 B1            *)
(*                                                                           *)
(* These are the REQUIRED theorems.  Structural mueq may change EnumT/Pi     *)
(* components, so the premise is the honest component-changing simulation    *)
(* (mueq_enumt_sim_components / mueq_pi_sim_components): the transported     *)
(* representation may carry a DIFFERENT component, related to the source     *)
(* component by qconv.  The component qconv is accumulated along the whole   *)
(* qconv chain with qconv_trans; at the final syntactic endpoint the         *)
(* stable-endpoint cancellation (cjoin_enumt_inv_glm / cjoin_pi_inv)         *)
(* relates the carried component to the endpoint components by cjoin, and    *)
(* the two relations are composed (qconv_trans) and converted back to conv   *)
(* via qconv_conv.                                                           *)
(*                                                                           *)
(* Pipeline:                                                                 *)
(*   1. conv → qconv                  (conv_qconv_glm)                       *)
(*   2. transport enumt_rep/pi_rep of the source endpoint along the qconv,   *)
(*      accumulating a component qconv                                       *)
(*      (cjoin links: cjoin algebra, component fixed; mueq links: the        *)
(*      component-changing simulation premise)                               *)
(*   3. both endpoints are now syntactic, so stable-endpoint cancellation    *)
(*      (cjoin_enumt_inv_glm / cjoin_pi_inv) extracts the component cjoin    *)
(*   4. compose accumulated qconv (source → carried) with the cancellation   *)
(*      cjoin (endpoint → carried) using qconv_trans / qconv_sym, and        *)
(*      convert back to conv via qconv_conv                                  *)
(* The simulation premise is a quantified hypothesis, so Print Assumptions   *)
(* is closed under the global context.                                       *)
(*                                                                           *)
(* The earlier fixed-component theorems conv_enumt_inj_from_sim_glm /        *)
(* conv_pi_inj_from_sim_glm are retained as SPECIAL CASES: their premise     *)
(* (mueq_enumt_sim / mueq_pi_sim) implies the honest component-changing one  *)
(* with a constant component (mueq_enumt_sim_subset / mueq_pi_sim_subset).   *)
(* They are generally unprovable from a mueq simulation alone because        *)
(* structural mueq may change EnumT/Pi components; new consumers must use    *)
(* the _component_sim_glm theorems.                                          *)

Require Import Progress.
Require Import _work_cjoin _work_cstep_invariants _luna_mueq
               _glm_qconv_def _glm_qconv_main
               _glm_injectivity_close_rep.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* --- exact EnumT injectivity, conditional on the honest EnumT simulation -- *)

Theorem conv_enumt_inj_from_component_sim_glm :
    mueq_enumt_sim_components ->
    forall E1 E2, conv (TEnumT E1) (TEnumT E2) -> conv E1 E2.
Proof.
  intros SIM E1 E2 Hconv.
  (* the source endpoint represents its own EnumT component *)
  assert (Hsrc : enumt_rep (TEnumT E1) E1) by apply cjoin_refl.
  (* step 2: carry the representation along the whole qconv chain,
     accumulating qconv E1 E' for the (possibly changed) component E' *)
  destruct (enumt_rep_qconv_components SIM (TEnumT E1) (TEnumT E2)
              (conv_qconv_glm _ _ Hconv) E1 Hsrc)
    as [E' [Hrep HqE]].
  (* step 3: stable-endpoint cancellation extracts cjoin E2 E' *)
  pose proof (cjoin_enumt_inv_glm _ _ Hrep) as Hcj.
  (* step 4: compose qconv E1 E' with the cancellation cjoin E2 E' and
     convert back to conv *)
  apply qconv_conv. eapply qconv_trans; [exact HqE |].
  eapply qconv_sym. apply cjoin_qconv. exact Hcj.
Qed.

(* --- exact Pi injectivity, conditional on the honest Pi simulation -------- *)

Theorem conv_pi_inj_from_component_sim_glm :
    mueq_pi_sim_components ->
    forall A0 B0 A1 B1,
      conv (TPi A0 B0) (TPi A1 B1) -> conv A0 A1 /\ conv B0 B1.
Proof.
  intros SIM A0 B0 A1 B1 Hconv.
  assert (Hsrc : pi_rep (TPi A0 B0) A0 B0) by apply cjoin_refl.
  destruct (pi_rep_qconv_components SIM (TPi A0 B0) (TPi A1 B1)
              (conv_qconv_glm _ _ Hconv) A0 B0 Hsrc)
    as [A' [B' [Hrep [HqA HqB]]]].
  (* stable-endpoint cancellation for TPi: cjoin A1 A' and cjoin B1 B' *)
  destruct (cjoin_pi_inv _ _ _ _ Hrep) as [HA HB].
  split.
  - apply qconv_conv. eapply qconv_trans; [exact HqA |].
    eapply qconv_sym. apply cjoin_qconv. exact HA.
  - apply qconv_conv. eapply qconv_trans; [exact HqB |].
    eapply qconv_sym. apply cjoin_qconv. exact HB.
Qed.

(* ========================================================================== *)
(*  SPECIAL CASES (retained, not for new consumers)                           *)
(*                                                                            *)
(*  The fixed-component theorems follow from the component-changing ones by   *)
(*  instantiating the moved component with the original one (qconv_refl).     *)
(*  Their premises are generally unprovable since structural mueq may change  *)
(*  EnumT/Pi components.                                                      *)
(* ========================================================================== *)

Theorem conv_enumt_inj_from_sim_glm :
    mueq_enumt_sim ->
    forall E1 E2, conv (TEnumT E1) (TEnumT E2) -> conv E1 E2.
Proof.
  intros SIM. apply conv_enumt_inj_from_component_sim_glm.
  apply mueq_enumt_sim_subset. exact SIM.
Qed.

Theorem conv_pi_inj_from_sim_glm :
    mueq_pi_sim ->
    forall A0 B0 A1 B1,
      conv (TPi A0 B0) (TPi A1 B1) -> conv A0 A1 /\ conv B0 B1.
Proof.
  intros SIM. apply conv_pi_inj_from_component_sim_glm.
  apply mueq_pi_sim_subset. exact SIM.
Qed.

Print Assumptions conv_enumt_inj_from_component_sim_glm.
Print Assumptions conv_pi_inj_from_component_sim_glm.
Print Assumptions conv_enumt_inj_from_sim_glm.
Print Assumptions conv_pi_inj_from_sim_glm.
