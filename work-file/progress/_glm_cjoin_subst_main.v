(* GLM worker 1 — cjoin-subst bundle, main: cjoin substitution and the
   stable-sort special case. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _glm_cjoin_subst_pstep _glm_cjoin_subst_epstep _glm_cjoin_subst_cstep.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules.

Theorem cjoin_subst_glm : forall t u, cjoin t u -> forall a k,
    cjoin (subst a k t) (subst a k u).
Proof.
  intros t u [w [Htw Huw]] a k.
  exists (subst a k w). split.
  - apply rtc_cstep_subst_same_glm. exact Htw.
  - apply rtc_cstep_subst_same_glm. exact Huw.
Qed.

Theorem cjoin_subst_sort_glm : forall B j, cjoin B (TSort j) -> forall a k,
    cjoin (subst a k B) (TSort j).
Proof.
  intros B j H a k.
  pose proof (cjoin_subst_glm B (TSort j) H a k) as H'.
  cbn [subst] in H'. exact H'.
Qed.

Print Assumptions cjoin_subst_glm.
Print Assumptions cjoin_subst_sort_glm.

Check cjoin_subst_glm :
  forall t u, cjoin t u -> forall a k,
    cjoin (subst a k t) (subst a k u).
Check cjoin_subst_sort_glm :
  forall B j, cjoin B (TSort j) -> forall a k,
    cjoin (subst a k B) (TSort j).
