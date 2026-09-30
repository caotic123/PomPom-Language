(* GLM worker 1 — conv-lift bundle, part 4 (main): conversion commutes with *)
(* de Bruijn lifting.                                                       *)
(*                                                                          *)
(*   conv_lift_glm : forall t u, conv t u -> forall d k,                    *)
(*                     conv (lift d k t) (lift d k u)                       *)
(*                                                                          *)
(* by induction on conv: cv_step via step_lift_glm, cv_eta via              *)
(* lift_lift_one_zero, congruences structurally, cv_phi with the closed     *)
(* eval/spine helpers (parts 1 and 3) and the definitional unfolding of     *)
(* labels/branches, and the case-branch congruence via map_app.             *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules Progress.
Require Import _glm_step_lift _glm_neutral_lift _glm_desc_against_lift
               _glm_spine_phi_lift _glm_conv_lift_bundle_eval
               _glm_conv_lift_bundle_desc _glm_conv_lift_bundle_spine.

(* Lifting commutes with the eta-branch shape, using lift_lift_one_zero     *)
(* (lift d (S k) (lift 1 0 S) = lift 1 0 (lift d k S)) and the fact that    *)
(* the bound TVar 0 is untouched; branches/labels unfold definitionally.    *)
Lemma eta_branch_lift : forall (S : term) (d k : nat),
    lift d k (TLam (branches (TApp (lift 1 0 S) (TVar 0)))) =
    TLam (branches (TApp (lift 1 0 (lift d k S)) (TVar 0))).
Proof.
  intros S d k. cbn [lift branches].
  rewrite lift_lift_one_zero. reflexivity.
Qed.

Theorem conv_lift_glm : forall t u, conv t u -> forall d k,
    conv (lift d k t) (lift d k u).
Proof.
  intros t u H.
  induction H; intros d kk; cbn.
  - (* cv_step : reduction commutes with lifting *)
    apply cv_step. apply (step_lift_glm t u H d kk).
  - (* cv_refl *)
    apply cv_refl.
  - (* cv_sym *)
    apply cv_sym. exact (IHconv d kk).
  - (* cv_trans *)
    eapply cv_trans; [exact (IHconv1 d kk) | exact (IHconv2 d kk)].
  - (* cv_eta : the lifted branch has the same shape, via lift_lift_one_zero *)
    rewrite lift_lift_one_zero. apply cv_eta.
  - (* cv_phi : Eqφ pruning — closed eval/spine helpers + unfolding of
       labels/branches *)
    eapply cv_phi.
    + (* branch family: lifted form of the premise, via eta_branch_lift *)
      rewrite <- (eta_branch_lift S1 d kk), <- (eta_branch_lift S2 d kk).
      exact (IHconv1 d kk).
    + (* labels (TApp (lift S1) (lift i)) = lift (labels (TApp S1 i)) *)
      exact (eval_lift_glm (labels (TApp S1 i)) Phi1 H0 d kk).
    + exact (eval_lift_glm (labels (TApp S2 i)) Phi2 H1 d kk).
    + exact (spine_phi_lift_glm_closed S1 i Phi1 Psi1 H2 d kk).
    + exact (spine_phi_lift_glm_closed S2 i Phi2 Psi2 H3 d kk).
    + exact (IHconv2 d kk).
  - (* cv_pi *)  apply cv_pi; eauto.
  - (* cv_lam *) apply cv_lam; eauto.
  - (* cv_app *) apply cv_app; eauto.
  - (* cv_sigma *) apply cv_sigma; eauto.
  - (* cv_pair *) apply cv_pair; eauto.
  - (* cv_fst *) apply cv_fst; eauto.
  - (* cv_snd *) apply cv_snd; eauto.
  - (* cv_conse *) apply cv_conse; eauto.
  - (* cv_enumt *) apply cv_enumt; eauto.
  - (* cv_esucc *) apply cv_esucc; eauto.
  - (* cv_epi *) apply cv_epi; eauto.
  - (* cv_switch *) apply cv_switch; eauto.
  - (* cv_idesc *) apply cv_idesc; eauto.
  - (* cv_ivar *) apply cv_ivar; eauto.
  - (* cv_iprod *) apply cv_iprod; eauto.
  - (* cv_ipi *) apply cv_ipi; eauto.
  - (* cv_isig *) apply cv_isig; eauto.
  - (* cv_ichoice *) apply cv_ichoice; eauto.
  - (* cv_interp *) apply cv_interp; eauto.
  - (* cv_mui *) apply cv_mui; eauto.
  - (* cv_mus *) apply cv_mus; eauto.
  - (* cv_in *) apply cv_in; eauto.
  - (* cv_ind *) apply cv_ind; eauto.
  - (* cv_iall *) apply cv_iall; eauto.
  - (* cv_hyps *) apply cv_hyps; eauto.
  - (* cv_list *) apply cv_list; eauto.
  - (* cv_lnil *) apply cv_lnil; eauto.
  - (* cv_lcons *) apply cv_lcons; eauto.
  - (* cv_case *) apply cv_case; eauto.
  - (* cv_case_br : map distributes over the branch context *)
    rewrite !map_app. cbn [map].
    apply cv_case_br; eauto.
Qed.

Check conv_lift_glm :
  forall t u, conv t u -> forall d k, conv (lift d k t) (lift d k u).
