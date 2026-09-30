(* ========================================================================== *)
(*  No-confusion for TEnumT payloads: cons vs nil (GLM worker 3).             *)
(*                                                                            *)
(*  Route (no conv_enumt_inj, no Progress.v conjecture):                      *)
(*   1. conv_phi_cjoin  : conv -> cjoin between phi-erased EnumT endpoints;   *)
(*   2. cjoin_enumt_inv_glm : cancel the stable TEnumT head, payload cjoin;   *)
(*   3. phi_erase preserves the outer TConsE / TNilE shape;                   *)
(*   4. cstep cannot leave the head (rtc_cstep_hshape), so the join witness   *)
(*      would carry both HConsE and HNilE heads -> hshape_tag_unique          *)
(*      yields HConsE = HNilE, a constructor clash.                           *)
(* ========================================================================== *)

Require Import Progress.
Require Import _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma conv_enumt_cons_nil_absurd_glm :
  forall tg E,
    conv (TEnumT (TConsE tg E)) (TEnumT TNilE) -> False.
Proof.
  intros tg E Hc.
  (* 1+3. erase phi: the conversion becomes a cjoin between the erased
     payloads, still of the shapes TConsE .. and TNilE. *)
  assert (Hj : cjoin (TConsE (phi_erase tg) (phi_erase E)) TNilE).
  { apply (cjoin_enumt_inv_glm _ _).
    cbn. exact (conv_phi_cjoin _ _ Hc). }
  (* 2. the join witness must be reachable from both endpoints. *)
  destruct Hj as [w [H1 H2]].
  (* 4. cstep preserves the head tag, so w has both heads. *)
  pose proof (rtc_cstep_hshape _ _ H1 HConsE (hs_conse _ _)) as Hh1.
  pose proof (rtc_cstep_hshape _ _ H2 HNilE hs_nile) as Hh2.
  pose proof (hshape_tag_unique _ _ _ Hh1 Hh2) as Hd.
  discriminate Hd.
Qed.

Lemma conv_enumt_nil_cons_absurd_glm :
  forall tg E,
    conv (TEnumT TNilE) (TEnumT (TConsE tg E)) -> False.
Proof.
  intros tg E Hc.
  apply (conv_enumt_cons_nil_absurd_glm tg E).
  apply cv_sym. exact Hc.
Qed.

Print Assumptions conv_enumt_cons_nil_absurd_glm.
Print Assumptions conv_enumt_nil_cons_absurd_glm.
