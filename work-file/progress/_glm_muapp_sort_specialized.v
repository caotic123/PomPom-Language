(* ========================================================================== *)
(*  _glm_muapp_sort_specialized.v — GLM worker 3: muapp_sort under the        *)
(*  specialized sort-target substitution interface.                           *)
(*                                                                            *)
(*  This file replaces the over-strong [conv_subst_compatible] premise of     *)
(*  [_glm_muapp_sort_close.v] by exactly the specialized interface            *)
(*                                                                            *)
(*    conv_subst_sort_target_compatible_glm :=                                *)
(*      forall B j, conv B (TSort j) ->                                       *)
(*      forall a k, conv (subst a k B) (TSort j).                             *)
(*                                                                            *)
(*  i.e. substituting into a sort-convertible type keeps it sort-convertible  *)
(*  (at the same sort level).  The Pi-codomain interface is kept verbatim:    *)
(*                                                                            *)
(*    conv_pi_codomain_compatible_glm :=                                      *)
(*      forall A0 B0 A1 B1, conv (TPi A0 B0) (TPi A1 B1) -> conv B0 B1.       *)
(*                                                                            *)
(*  Everything else is reused from the closed bundles: the conv-side          *)
(*  invariant [sub_pi_cod_sort_inv_glm], the extraction lemma                 *)
(*  [sub_pisort0_cod_sort_glm], the disjointness helpers, and the whole       *)
(*  app-origin / value inversion architecture of _glm_muapp_sort_origin.v     *)
(*  and _glm_muapp_sort_close.v ([check_app_origin],                          *)
(*  [app_origin_sort_split_glm], [value_app_mu_inv_glm], [ao_chk_sort_glm]).  *)
(*                                                                            *)
(*  The only places the substitution interface is consumed are the specialized*)
(*  codomain transport [subst_cod_sort_spec_glm] and the two specialized      *)
(*  ao_chk branch closers [ao_chk_mui_sort_spec_glm] /                        *)
(*  [ao_chk_mus_sort_spec_glm] — each a small named lemma.                    *)
(*                                                                            *)
(*  No Axiom / Conjecture / Admitted / admit / Abort; no Progress.v           *)
(*  conjecture is used (conv_whd occurrences go through the fully proved      *)
(*  [conv_whd_proved] of _work_conv_whd_pos.v).  The two compatibilities are  *)
(*  binders of the final theorem, not axioms:                                 *)
(*    Print Assumptions muapp_sort_from_specialized_compat_glm.               *)
(*  reports "Closed under the global context".                                *)
(* ========================================================================== *)

Require Import Progress _work_conv_whd_pos _glm_muapp_sort_origin
  _glm_muapp_sort_close.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* The exactly-two conversion interfaces for this file: the kept Pi-codomain
   injectivity (re-exported from the close bundle for local reference) and the
   NEW specialized sort-target substitution interface, replacing
   conv_subst_compatible. *)
Definition conv_pi_codomain_compatible_glm' : Prop :=
  forall A0 B0 A1 B1, conv (TPi A0 B0) (TPi A1 B1) -> conv B0 B1.

Definition conv_subst_sort_target_compatible_glm : Prop :=
  forall B j, conv B (TSort j) ->
  forall a k, conv (subst a k B) (TSort j).

(* The two definitions of Pi-codomain compatibility agree definitionally. *)
Lemma conv_pi_codomain_compat_unfold_glm :
  conv_pi_codomain_compatible_glm' <-> conv_pi_codomain_compatible_glm.
Proof. split; exact (fun H => H). Qed.

(* ========================================================================== *)
(*  (S1) Specialized codomain transport.                                      *)
(*                                                                            *)
(*  This is the specialized replacement of [subst_cod_sort_glm]: where the    *)
(*  old closer had to push a conversion pair through an arbitrary substitution*)
(*  (conv_subst_compatible at (cv_sym Hj, cv_refl)), the specialized interface *)
(*  delivers the result directly, for any level.                              *)
(* ========================================================================== *)

Lemma subst_sort_target_spec_glm :
  conv_subst_sort_target_compatible_glm ->
  forall a k B j, conv B (TSort j) -> conv (subst a k B) (TSort j).
Proof.
  intros Hspec a k B j Hj. exact (Hspec B j Hj a k).
Qed.

Lemma subst_cod_sort_spec_glm :
  conv_subst_sort_target_compatible_glm ->
  forall a B j, conv B (TSort j) -> conv (subst a 0 B) (TSort j).
Proof.
  intros Hspec a B j Hj. exact (Hspec B j Hj a 0).
Qed.

(* ========================================================================== *)
(*  (S2) The specialized ao_chk branch closers.                               *)
(*                                                                            *)
(*  Same architecture as [ao_chk_mui_sort_glm]/[ao_chk_mus_sort_glm] of the   *)
(*  close bundle, but consuming only the specialized interface.  Both use     *)
(*  [check_mui_synth_glm]/[check_mus_synth_glm] (origin bundle) for the       *)
(*  check inversion, [sub_pisort0_cod_sort_glm] (close bundle) for the sub    *)
(*  case, and [ao_chk_sort_glm] (origin bundle) for the finish.               *)
(* ========================================================================== *)

Lemma ao_chk_mui_sort_spec_glm :
  conv_pi_codomain_compatible_glm ->
  conv_subst_sort_target_compatible_glm ->
  forall R a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuI R) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hcomp Hspec R a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mui_synth_glm [] (TMuI R) (TPi A B) Hf R eq_refl) as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - (* conv case: Pi-injectivity at the source, then the specialized
         sort-target transport *)
      exists 0. apply (Hspec B 0 (cv_sym (Hcomp IT (TSort 0) A B Hrel)) a 0).
    - (* sub case: the extraction lemma, then the specialized transport *)
      destruct (sub_pisort0_cod_sort_glm Hcomp [] IT A B Hrel) as [j Hj].
      exists j. apply (Hspec B j Hj a 0). }
  eapply ao_chk_sort_glm; eassumption.
Qed.

Lemma ao_chk_mus_sort_spec_glm :
  conv_pi_codomain_compatible_glm ->
  conv_subst_sort_target_compatible_glm ->
  forall Sf a A B k T U h,
    check [] (TPi A B) (TSort k) -> check [] (TMuS Sf) (TPi A B) ->
    check [] a A -> sub [] (subst a 0 B) T -> conv T U -> whd U h ->
    h = HSort.
Proof.
  intros Hcomp Hspec Sf a A B k T U h Hk Hf Ha Hsub Hc Hw.
  destruct (check_mus_synth_glm [] (TMuS Sf) (TPi A B) Hf Sf eq_refl) as [IT [Hsyn Hrel]].
  assert (Hs : exists j, conv (subst a 0 B) (TSort j)).
  { destruct Hrel as [Hrel | Hrel].
    - exists 0. apply (Hspec B 0 (cv_sym (Hcomp IT (TSort 0) A B Hrel)) a 0).
    - destruct (sub_pisort0_cod_sort_glm Hcomp [] IT A B Hrel) as [j Hj].
      exists j. apply (Hspec B j Hj a 0). }
  eapply ao_chk_sort_glm; eassumption.
Qed.

(* ========================================================================== *)
(*  (S3) The required conditional theorem.                                    *)
(*                                                                            *)
(*  The app-origin / value inversion architecture is reused verbatim from the *)
(*  close bundle: [check_app_origin] splits on ao_syn (closed by              *)
(*  [ao_syn_branch_glm] of the origin bundle) and ao_chk (closed above, via   *)
(*  [value_app_mu_inv_glm] forcing the head to be a value mu-former).         *)
(* ========================================================================== *)

Theorem muapp_sort_from_specialized_compat_glm :
  conv_pi_codomain_compatible_glm ->
  conv_subst_sort_target_compatible_glm ->
  forall f a T U h,
    check [] (TApp f a) T -> value (TApp f a) ->
    conv T U -> whd U h -> h = HSort.
Proof.
  intros Hcomp Hspec f a T U h Hchk Hv Hc Hw.
  destruct (check_app_origin [] (TApp f a) T Hchk eq_refl f a eq_refl)
    as [X [Hor Hsub]].
  destruct (app_origin_sort_split_glm f a X T U h Hor Hv Hsub Hc Hw)
    as [Hdone | [A [B [k [HX [Hk [Hf Ha]]]]]]].
  - (* ao_syn: the synthesis branch, closed in the origin bundle *)
    exact Hdone.
  - (* ao_chk: the value application's head is a mu-former *)
    subst X.
    destruct (value_app_mu_inv_glm _ _ Hv) as [[R Hf'] | [Sf Hf']].
    + rewrite Hf' in Hf.
      eapply ao_chk_mui_sort_spec_glm; eassumption.
    + rewrite Hf' in Hf.
      eapply ao_chk_mus_sort_spec_glm; eassumption.
Qed.

(* Assumption audit — all must report: Closed under the global context. *)
Print Assumptions subst_sort_target_spec_glm.
Print Assumptions subst_cod_sort_spec_glm.
Print Assumptions ao_chk_mui_sort_spec_glm.
Print Assumptions ao_chk_mus_sort_spec_glm.
Print Assumptions muapp_sort_from_specialized_compat_glm.
