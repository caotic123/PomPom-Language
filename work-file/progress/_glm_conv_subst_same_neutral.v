(* GLM worker 1 — conv-subst layer 2: same-substituent transport of conv,    *)
(* under a NEUTRAL substituent.                                             *)
(*                                                                          *)
(*   conv_subst_same_neutral_glm : conv t t' -> neutral u -> forall k,      *)
(*                    conv (subst u k t) (subst u k t')                     *)
(*                                                                          *)
(* Induction on the conv derivation, mirroring _glm_conv_lift_bundle_main:  *)
(*  - cv_step via step_subst_glm (the closed step bundle),                  *)
(*  - cv_eta via subst_eta_shape_glm (substitution keeps the eta shape),    *)
(*  - congruences structurally (branches via map_app + cv_case_br),         *)
(*  - cv_phi via eval_subst_glm + spine_phi_subst_glm (which requires       *)
(*    exactly the neutral-u premise) + subst_eta_branch_glm.                *)
(*                                                                          *)
(* Neutrality is needed ONLY for cv_phi's spine transport: a neutral tail   *)
(* TVar k becomes lift k 0 u, which stays neutral exactly because u is.     *)
(* For arbitrary (non-convertible-to-neutral) u the cv_phi case is the      *)
(* genuine residual of conv_subst_compatible_glm — see                      *)
(* _glm_conv_subst_main.v, where the exact theorem is reduced to that       *)
(* single residual constructor case.                                        *)

Require Import TypeRules Progress.
Require Import _glm_subst_reduction_bundle_step _glm_subst_reduction_bundle_eval
               _glm_subst_reduction_bundle_sem _glm_subst_reduction_bundle_spine
               _glm_conv_subst_algebra.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Theorem conv_subst_same_neutral_glm : forall t t' : term, conv t t' ->
    forall u : term, neutral u -> forall k : nat,
      conv (subst u k t) (subst u k t').
Proof.
  intros t u H.
  induction H; intros u0 Hunat kk; cbn.
  - (* cv_step *)
    apply cv_step. exact (step_subst_glm _ _ H u0 kk).
  - (* cv_refl *) apply cv_refl.
  - (* cv_sym *) apply cv_sym. exact (IHconv u0 Hunat kk).
  - (* cv_trans *) eapply cv_trans; [exact (IHconv1 u0 Hunat kk) | exact (IHconv2 u0 Hunat kk)].
  - (* cv_eta *)
    rewrite subst_lift_one_zero. apply cv_eta.
  - (* cv_phi *)
    eapply cv_phi.
    + (* branch family *)
      rewrite <- !subst_eta_branch_glm. exact (IHconv1 u0 Hunat kk).
    + exact (eval_subst_glm (labels (TApp S1 i)) Phi1 H0 u0 kk).
    + exact (eval_subst_glm (labels (TApp S2 i)) Phi2 H1 u0 kk).
    + exact (spine_phi_subst_glm S1 i Phi1 Psi1 H2 u0 kk Hunat).
    + exact (spine_phi_subst_glm S2 i Phi2 Psi2 H3 u0 kk Hunat).
    + exact (IHconv2 u0 Hunat kk).
  - (* cv_pi *)  apply cv_pi; eauto.
  - (* cv_lam *) apply cv_lam. exact (IHconv u0 Hunat (S kk)).
  - (* cv_app *) apply cv_app; eauto.
  - (* cv_sigma *) apply cv_sigma; eauto.
  - (* cv_pair *) apply cv_pair; eauto.
  - (* cv_fst *) apply cv_fst. exact (IHconv u0 Hunat kk).
  - (* cv_snd *) apply cv_snd. exact (IHconv u0 Hunat kk).
  - (* cv_conse *) apply cv_conse; eauto.
  - (* cv_enumt *) apply cv_enumt. exact (IHconv u0 Hunat kk).
  - (* cv_esucc *) apply cv_esucc. exact (IHconv u0 Hunat kk).
  - (* cv_epi *) apply cv_epi; eauto.
  - (* cv_switch *) apply cv_switch; eauto.
  - (* cv_idesc *) apply cv_idesc. exact (IHconv u0 Hunat kk).
  - (* cv_ivar *) apply cv_ivar. exact (IHconv u0 Hunat kk).
  - (* cv_iprod *) apply cv_iprod; eauto.
  - (* cv_ipi *) apply cv_ipi; eauto.
  - (* cv_isig *) apply cv_isig; eauto.
  - (* cv_ichoice *) apply cv_ichoice; eauto.
  - (* cv_interp *) apply cv_interp; eauto.
  - (* cv_mui *) apply cv_mui. exact (IHconv u0 Hunat kk).
  - (* cv_mus *) apply cv_mus. exact (IHconv u0 Hunat kk).
  - (* cv_in *) apply cv_in. exact (IHconv u0 Hunat kk).
  - (* cv_ind *) apply cv_ind; eauto.
  - (* cv_iall *) apply cv_iall; eauto.
  - (* cv_hyps *) apply cv_hyps; eauto.
  - (* cv_list *) apply cv_list. exact (IHconv u0 Hunat kk).
  - (* cv_lnil *) apply cv_lnil. exact (IHconv u0 Hunat kk).
  - (* cv_lcons *) apply cv_lcons; eauto.
  - (* cv_case *) apply cv_case; eauto.
  - (* cv_case_br *)
    rewrite !map_app. cbn [map].
    apply cv_case_br; eauto.
Qed.

Check conv_subst_same_neutral_glm :
  forall t t' : term, conv t t' ->
    forall u : term, neutral u -> forall k : nat,
      conv (subst u k t) (subst u k t').
