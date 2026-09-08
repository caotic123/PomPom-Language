(* GLM worker 1 — conv-subst layer 4: neutrality only AT THE CUTOFF, and     *)
(* only on ONE side.                                                        *)
(*                                                                          *)
(* The cv_phi spine transport needs neutral (subst u k Phin) for the        *)
(* sph_neutral case.  A neutral tail mentions the substituted variable k    *)
(* only at TVar k positions, which become lift k 0 u; every other position  *)
(* stays a variable or lowers.  So the exact requirement is                 *)
(*   neutral (lift k 0 u)                                                   *)
(* — strictly weaker than `neutral u` (e.g. u = TVar 5 is not neutral-      *)
(* relevant only through its lifted form... in fact neutral u IMPLIES       *)
(* neutral (lift k 0 u) by neutral_lift_glm, but e.g. u = TApp (TVar 3) x  *)
(* has neutral lift while its neutrality is the same; the real gain is      *)
(* statements where only the cutoff-k lifted form is required).             *)
(*                                                                          *)
(* Deliverables:                                                            *)
(*   neutral_subst_neutralat_glm   : neutral t -> neutral (lift k 0 u)      *)
(*                                   -> neutral (subst u k t)               *)
(*   spine_phi_subst_neutralat_glm : spine_phi transport under neutralat    *)
(*   conv_subst_same_neutralat_glm : conv t t' fixed-substituent transport  *)
(*   conv_subst_one_neutralat_glm  : FULL two-sided theorem with only the   *)
(*     FIRST substituent required to satisfy neutral (lift k 0 u) — the     *)
(*     second substituent is arbitrary (the second leg of the chain is the  *)
(*     unconditional rigid swap).                                           *)

Require Import TypeRules Progress.
Require Import _glm_subst_reduction_bundle_step _glm_subst_reduction_bundle_eval
               _glm_subst_reduction_bundle_sem _glm_subst_reduction_bundle_spine
               _glm_conv_subst_algebra _glm_conv_subst_rigid
               _glm_neutral_lift.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Theorem neutral_subst_neutralat_glm : forall t, neutral t ->
    forall u k, neutral (lift k 0 u) -> neutral (subst u k t).
Proof.
  intros t H.
  induction H as
    [ n
    | f a Hf IHf
    | p Hp IHp
    | p Hp IHp
    | E P p e He IHe
    | R P stp i x Hx IHx
    | M Q bs HM IHM ]; intros u k Hunat; cbn [subst].
  - (* ne_var *)
    destruct (Nat.ltb n k) eqn:Hlt; [apply ne_var |].
    destruct (Nat.eqb n k) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst n. exact Hunat.
    + apply ne_var.
  - apply ne_app. exact (IHf u k Hunat).
  - apply ne_fst. exact (IHp u k Hunat).
  - apply ne_snd. exact (IHp u k Hunat).
  - apply ne_switch. exact (IHe u k Hunat).
  - apply ne_ind. exact (IHx u k Hunat).
  - apply ne_case. exact (IHM u k Hunat).
Qed.


(* lift only shifts variable indices, so neutrality of the lifted form is    *)
(* cutoff-independent:                                                       *)
(*   neutral (lift k 0 u) -> neutral (lift (S k) 0 u)                        *)
Theorem neutral_lift_up_glm : forall u : term, forall k : nat,
    neutral (lift k 0 u) -> neutral (lift (S k) 0 u).
Proof.
  induction u; intros kk H; cbn [lift] in H |- *.
  - (* TVar *) apply ne_var.
  - (* TSort *) inversion H.
  - (* TPi *) inversion H.
  - (* TLam *) inversion H.
  - (* TApp *) inversion H; subst; apply ne_app; apply IHu1; exact H1.
  - (* TSigma *) inversion H.
  - (* TPair *) inversion H.
  - (* TFst *) inversion H; subst; apply ne_fst; apply IHu; exact H1.
  - (* TSnd *) inversion H; subst; apply ne_snd; apply IHu; exact H1.
  - (* TUnitT *) inversion H.
  - (* TUnit *) inversion H.
  - (* TUId *) inversion H.
  - (* TTag *) inversion H.
  - (* TEnumU *) inversion H.
  - (* TNilE *) inversion H.
  - (* TConsE *) inversion H.
  - (* TEnumT *) inversion H.
  - (* TEZero *) inversion H.
  - (* TESucc *) inversion H.
  - (* TEPi *) inversion H.
  - (* TSwitch *) inversion H; subst; apply ne_switch; apply IHu4; assumption.
  - (* TIDesc *) inversion H.
  - (* TIVar *) inversion H.
  - (* TI1 *) inversion H.
  - (* TIProd *) inversion H.
  - (* TIPi *) inversion H.
  - (* TISig *) inversion H.
  - (* TIChoice *) inversion H.
  - (* TInterp *) inversion H.
  - (* TMuI *) inversion H.
  - (* TMuS *) inversion H.
  - (* TIn *) inversion H.
  - (* TInd *) inversion H; subst; apply ne_ind; apply IHu5; assumption.
  - (* TIAll *) inversion H.
  - (* THyps *) inversion H.
  - (* TList *) inversion H.
  - (* TLNil *) inversion H.
  - (* TLCons *) inversion H.
  - (* TCase *) inversion H; subst; apply ne_case; apply IHu1; assumption.
Qed.

Theorem spine_phi_subst_neutralat_glm :
  forall (Sf i Phi Psi : term),
    spine_phi Sf i Phi Psi ->
    forall (u : term) (k : nat),
      neutral (lift k 0 u) ->
      spine_phi (subst u k Sf) (subst u k i) (subst u k Phi) (subst u k Psi).
Proof.
  intros Sf i Phi Psi H.
  induction H as
    [ Phi0 A Heval
    | Phi0 A c Phi' Psi' Heval Hsp IH
    | Phi0 A c Phi' Psi' Heval Hdesc Hsp IH
    | Phi0 Phin Heval Hneu ]; intros u k Hunat.
  - (* sph_nil *)
    apply (@sph_nil (subst u k Sf) (subst u k i)
                    (subst u k Phi0) (subst u k A)).
    exact (eval_subst_glm _ _ Heval u k).
  - (* sph_keep *)
    apply (@sph_keep (subst u k Sf) (subst u k i) (subst u k Phi0)
                     (subst u k A) (subst u k c) (subst u k Phi')
                     (subst u k Psi')).
    + exact (eval_subst_glm _ _ Heval u k).
    + exact (IH u k Hunat).
  - (* sph_drop *)
    apply (@sph_drop (subst u k Sf) (subst u k i) (subst u k Phi0)
                     (subst u k A) (subst u k c) (subst u k Phi')
                     (subst u k Psi')).
    + exact (eval_subst_glm _ _ Heval u k).
    + rewrite subst_branch_app_glm.
      exact (desc_against_subst_glm _ Hdesc u k).
    + exact (IH u k Hunat).
  - (* sph_neutral *)
    apply (@sph_neutral (subst u k Sf) (subst u k i)
                        (subst u k Phi0) (subst u k Phin)).
    + exact (eval_subst_glm _ _ Heval u k).
    + exact (neutral_subst_neutralat_glm _ Hneu u k Hunat).
Qed.

Theorem conv_subst_same_neutralat_glm : forall t t' : term, conv t t' ->
    forall u : term, forall k : nat, neutral (lift k 0 u) ->
      conv (subst u k t) (subst u k t').
Proof.
  intros t t' H.
  induction H; intros u0 kk Hunat; cbn.
  - (* cv_step *)
    apply cv_step. exact (step_subst_glm _ _ H u0 kk).
  - (* cv_refl *) apply cv_refl.
  - (* cv_sym *) apply cv_sym. exact (IHconv u0 kk Hunat).
  - (* cv_trans *)
    eapply cv_trans; [exact (IHconv1 u0 kk Hunat) | exact (IHconv2 u0 kk Hunat)].
  - (* cv_eta *)
    rewrite subst_lift_one_zero. apply cv_eta.
  - (* cv_phi *)
    eapply cv_phi.
    + rewrite <- !subst_eta_branch_glm. exact (IHconv1 u0 kk Hunat).
    + exact (eval_subst_glm (labels (TApp S1 i)) Phi1 H0 u0 kk).
    + exact (eval_subst_glm (labels (TApp S2 i)) Phi2 H1 u0 kk).
    + exact (spine_phi_subst_neutralat_glm S1 i Phi1 Psi1 H2 u0 kk Hunat).
    + exact (spine_phi_subst_neutralat_glm S2 i Phi2 Psi2 H3 u0 kk Hunat).
    + exact (IHconv2 u0 kk Hunat).
  - (* cv_pi *)  apply cv_pi;
      [exact (IHconv1 u0 kk Hunat)
      | exact (IHconv2 u0 (S kk) (neutral_lift_up_glm u0 kk Hunat))].
  - (* cv_lam *) apply cv_lam.
    exact (IHconv u0 (S kk) (neutral_lift_up_glm u0 kk Hunat)).
  - (* cv_app *) apply cv_app; eauto.
  - (* cv_sigma *) apply cv_sigma;
      [exact (IHconv1 u0 kk Hunat)
      | exact (IHconv2 u0 (S kk) (neutral_lift_up_glm u0 kk Hunat))].
  - (* cv_pair *) apply cv_pair; eauto.
  - (* cv_fst *) apply cv_fst. exact (IHconv u0 kk Hunat).
  - (* cv_snd *) apply cv_snd. exact (IHconv u0 kk Hunat).
  - (* cv_conse *) apply cv_conse; eauto.
  - (* cv_enumt *) apply cv_enumt. exact (IHconv u0 kk Hunat).
  - (* cv_esucc *) apply cv_esucc. exact (IHconv u0 kk Hunat).
  - (* cv_epi *) apply cv_epi; eauto.
  - (* cv_switch *) apply cv_switch; eauto.
  - (* cv_idesc *) apply cv_idesc. exact (IHconv u0 kk Hunat).
  - (* cv_ivar *) apply cv_ivar. exact (IHconv u0 kk Hunat).
  - (* cv_iprod *) apply cv_iprod; eauto.
  - (* cv_ipi *) apply cv_ipi; eauto.
  - (* cv_isig *) apply cv_isig; eauto.
  - (* cv_ichoice *) apply cv_ichoice; eauto.
  - (* cv_interp *) apply cv_interp; eauto.
  - (* cv_mui *) apply cv_mui. exact (IHconv u0 kk Hunat).
  - (* cv_mus *) apply cv_mus. exact (IHconv u0 kk Hunat).
  - (* cv_in *) apply cv_in. exact (IHconv u0 kk Hunat).
  - (* cv_ind *) apply cv_ind; eauto.
  - (* cv_iall *) apply cv_iall; eauto.
  - (* cv_hyps *) apply cv_hyps; eauto.
  - (* cv_list *) apply cv_list. exact (IHconv u0 kk Hunat).
  - (* cv_lnil *) apply cv_lnil. exact (IHconv u0 kk Hunat).
  - (* cv_lcons *) apply cv_lcons; eauto.
  - (* cv_case *)
    apply (@cv_case (subst u0 kk M) (subst u0 kk M') (subst u0 kk Q)
                    (subst u0 kk Q')
                    (map (fun '(c, b) => (subst u0 kk c, subst u0 (S kk) b)) bs)).
    + exact (IHconv1 u0 kk Hunat).
    + exact (IHconv2 u0 kk Hunat).
  - (* cv_case_br *)
    rewrite !map_app. cbn [map].
    apply cv_case_br;
      [ exact (IHconv1 u0 kk Hunat)
      | exact (IHconv2 u0 (S kk) (neutral_lift_up_glm u0 kk Hunat)) ].
Qed.

(* FULL two-sided theorem with only the FIRST substituent constrained:      *)
(*   conv t t' -> conv u u' -> neutral (lift k 0 u)                         *)
(*   -> conv (subst u k t) (subst u' k t')                                  *)
(* u' is completely arbitrary.                                              *)
Theorem conv_subst_one_neutralat_glm :
  forall t t' u u' : term, conv t t' -> conv u u' -> forall k : nat,
    neutral (lift k 0 u) -> conv (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' Ht Hu k Hunat.
  eapply cv_trans.
  - exact (conv_subst_same_neutralat_glm t t' Ht u k Hunat).
  - exact (conv_subst_rigid_glm u u' Hu t' k).
Qed.

(* Symmetric form: constrain the SECOND substituent instead. *)
Theorem conv_subst_one_neutralat_sym_glm :
  forall t t' u u' : term, conv t t' -> conv u u' -> forall k : nat,
    neutral (lift k 0 u') -> conv (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' Ht Hu k Hunat.
  apply cv_sym.
  apply (conv_subst_one_neutralat_glm t' t u' u (cv_sym Ht) (cv_sym Hu) k Hunat).
Qed.

(* And the pair form: each side constrained at the common cutoff. *)
Theorem conv_subst_neutralat_pair_glm :
  forall t t' u u' : term, conv t t' -> conv u u' -> forall k : nat,
    neutral (lift k 0 u) -> neutral (lift k 0 u') ->
    conv (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' Ht Hu k Hunat Hunat'.
  apply (conv_subst_one_neutralat_glm t t' u u' Ht Hu k Hunat).
Qed.

(* Plain neutrality of one side is the k-uniform special case. *)
Corollary conv_subst_one_neutral_strong_glm :
  forall t t' u u' : term, conv t t' -> conv u u' ->
    neutral u ->
    forall k : nat, conv (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' Ht Hu Hunat k.
  apply (conv_subst_one_neutralat_glm t t' u u' Ht Hu k
         (neutral_lift_glm u Hunat k 0)).
Qed.

Print Assumptions conv_subst_one_neutralat_glm.
Print Assumptions conv_subst_neutralat_pair_glm.
Print Assumptions conv_subst_one_neutral_strong_glm.
