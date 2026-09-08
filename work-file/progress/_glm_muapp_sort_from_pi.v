(* ========================================================================== *)
(*  _glm_muapp_sort_from_pi.v — GLM worker 4: muapp_sort conditional on       *)
(*  Pi-codomain injectivity ALONE, via the closed conv_subst0_glm.            *)
(*                                                                            *)
(*  The predecessor _glm_muapp_sort_close.v reduced muapp_sort to TWO         *)
(*  conversion interfaces: Pi-codomain injectivity (conv_pi_codomain_         *)
(*  compatible_glm) plus the unrestricted substitution compatibility          *)
(*  (conv_subst_compatible, arbitrary cutoff k).  That second premise is now  *)
(*  eliminated: _glm_conv_subst0.v proves the cutoff-0 instance               *)
(*                                                                            *)
(*     conv_subst0_glm : conv t t' -> conv a a' ->                            *)
(*                       conv (subst a 0 t) (subst a' 0 t')                   *)
(*                                                                            *)
(*  closed under the global context, and every use of substitution here is    *)
(*  at cutoff 0 with a fixed substituent — exactly its shape.  The remaining  *)
(*  single interface is Pi-codomain injectivity of conv, taken as a binder:   *)
(*                                                                            *)
(*    Theorem muapp_sort_from_pi_inj_glm :                                    *)
(*      conv_pi_codomain_compatible_glm ->                                    *)
(*      forall f a T U h,                                                     *)
(*        check [] (TApp f a) T -> value (TApp f a) ->                        *)
(*        conv T U -> whd U h -> h = HSort.                                   *)
(*                                                                            *)
(*  No Axiom / Conjecture / Admitted / admit / Abort; no Progress.v           *)
(*  conjecture (conv_whd enters only through the fully proved                 *)
(*  conv_whd_proved and the closed origin/close bundles).  No arbitrary-      *)
(*  cutoff or unrestricted conv-subst premise appears anywhere below.         *)
(*                                                                            *)
(*  Architecture (small named lemmas):                                        *)
(*    (1) subst0_sort_target_glm  — conv B (TSort j) ->                       *)
(*        conv (subst a 0 B) (TSort j), by conv_subst0_glm B (TSort j) a a    *)
(*        with cv_refl a; simplification leaves the sort unchanged.           *)
(*    (2) pisort0_conv_cod_glm    — the conv-case codomain extraction at      *)
(*        source TPi IT (TSort 0), by Pi-codomain injectivity.                *)
(*    (3) ao_chk_mui_sort_pi_glm / ao_chk_mus_sort_pi_glm — replacement      *)
(*        ao_chk branch closers (muI / muS formers), needing only the         *)
(*        Pi-injectivity binder.                                              *)
(*    (4) muapp_sort_from_pi_inj_glm — final theorem, via check_app_origin,   *)
(*        app_origin_sort_split_glm and value_app_mu_inv_glm.                 *)
(* ========================================================================== *)

Require Import Progress _work_conv_whd_pos _glm_muapp_sort_origin
  _glm_muapp_sort_close _glm_conv_subst0.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ========================================================================== *)
(*  (1) Cutoff-0 substitution transports sort-convertibility of a codomain.   *)
(* ========================================================================== *)

(* conv_subst0_glm B (TSort j) a a Hj (cv_refl a) yields
     conv (subst a 0 B) (subst a 0 (TSort j));
   simplification (subst u k (TSort s) = TSort s) leaves the sort unchanged. *)
Lemma subst0_sort_target_glm : forall a B j,
    conv B (TSort j) -> conv (subst a 0 B) (TSort j).
Proof.
  intros a B j Hj.
  pose proof (conv_subst0_glm B (TSort j) a a Hj (cv_refl a)) as H.
  cbn [subst] in H. exact H.
Qed.

(* ========================================================================== *)
(*  (2) The conv-case codomain extraction at a TPi IT (TSort 0) source.       *)
(* ========================================================================== *)

Lemma pisort0_conv_cod_glm :
  conv_pi_codomain_compatible_glm ->
  forall IT A B, conv (TPi IT (TSort 0)) (TPi A B) -> conv B (TSort 0).
Proof.
  intros Hcomp IT A B Hrel.
  apply cv_sym. apply (Hcomp IT (TSort 0) A B Hrel).
Qed.

(* ========================================================================== *)
(*  (3) Replacement ao_chk branch closers — Pi-injectivity binder only.       *)
(* ========================================================================== *)

Lemma ao_chk_mui_sort_pi_glm :
  conv_pi_codomain_compatible_glm ->
  forall R a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuI R) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hcomp R a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mui_synth_glm [] (TMuI R) (TPi A B) Hf R eq_refl)
    as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - (* conv case: Pi-codomain injectivity, then cutoff-0 substitution *)
      exists 0. eapply subst0_sort_target_glm.
      eapply pisort0_conv_cod_glm; [exact Hcomp | exact Hrel].
    - (* sub case: the closed subtyping-level Pi-codomain extraction *)
      destruct (sub_pisort0_cod_sort_glm Hcomp [] IT A B Hrel) as [j Hj].
      exists j. eapply subst0_sort_target_glm; exact Hj. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

Lemma ao_chk_mus_sort_pi_glm :
  conv_pi_codomain_compatible_glm ->
  forall Sf a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuS Sf) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hcomp Sf a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mus_synth_glm [] (TMuS Sf) (TPi A B) Hf Sf eq_refl)
    as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - exists 0. eapply subst0_sort_target_glm.
      eapply pisort0_conv_cod_glm; [exact Hcomp | exact Hrel].
    - destruct (sub_pisort0_cod_sort_glm Hcomp [] IT A B Hrel) as [j Hj].
      exists j. eapply subst0_sort_target_glm; exact Hj. }
  eapply ao_chk_sort_glm; eassumption.
Qed.

(* ========================================================================== *)
(*  (4) The full typing proof, conditional ONLY on Pi-codomain injectivity.   *)
(* ========================================================================== *)

Theorem muapp_sort_from_pi_inj_glm :
  conv_pi_codomain_compatible_glm ->
  forall f a T U h,
    check [] (TApp f a) T -> value (TApp f a) ->
    conv T U -> whd U h -> h = HSort.
Proof.
  intros Hcomp f a T U h Hchk Hv Hc Hw.
  destruct (check_app_origin [] (TApp f a) T Hchk eq_refl f a eq_refl)
    as [X [Hor Hsub]].
  destruct (app_origin_sort_split_glm f a X T U h Hor Hv Hsub Hc Hw)
    as [Hdone | [A [B [k [HX [Hk [Hf Ha]]]]]]].
  - (* ao_syn: the value application synthesizes Set_0; closed in the origin *)
    exact Hdone.
  - (* ao_chk: the value application's head is a mu-former *)
    subst X.
    destruct (value_app_mu_inv_glm _ _ Hv) as [[R Hf'] | [Sf Hf']].
    + rewrite Hf' in Hf.
      eapply ao_chk_mui_sort_pi_glm; eassumption.
    + rewrite Hf' in Hf.
      eapply ao_chk_mus_sort_pi_glm; eassumption.
Qed.

Print Assumptions ao_chk_mui_sort_pi_glm.
Print Assumptions ao_chk_mus_sort_pi_glm.
Print Assumptions muapp_sort_from_pi_inj_glm.
