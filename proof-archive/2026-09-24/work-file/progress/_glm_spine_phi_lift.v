Require Import TypeRules Progress.
Require Import _glm_neutral_lift _glm_desc_against_lift.

(* GLM worker 2: spine_phi is stable under de Bruijn lifting, assuming      *)
(* eval_lift_compatible_glm (via _glm_desc_against_lift / _glm_neutral_lift)*)

Lemma lift_branch_app_glm : forall (d k : nat) (Sf i c : term),
  TApp (branches (TApp (lift d k Sf) (lift d k i))) (lift d k c) =
  lift d k (TApp (branches (TApp Sf i)) c).
Proof.
  intros d k Sf i c. reflexivity.
Qed.

Section SpinePhiLiftGlm.

Hypothesis eval_lift_compat : eval_lift_compatible_glm.

Lemma eval_lift_lnil_glm : forall (d k : nat) (Phi A : term),
  eval Phi (TLNil A) ->
  eval (lift d k Phi) (TLNil (lift d k A)).
Proof.
  intros d k Phi A He.
  exact (eval_lift_compat d k Phi (TLNil A) He).
Qed.

Lemma eval_lift_lcons_glm : forall (d k : nat) (Phi A c Phi' : term),
  eval Phi (TLCons A c Phi') ->
  eval (lift d k Phi) (TLCons (lift d k A) (lift d k c) (lift d k Phi')).
Proof.
  intros d k Phi A c Phi' He.
  exact (eval_lift_compat d k Phi (TLCons A c Phi') He).
Qed.

Theorem spine_phi_lift_glm :
  forall (Sf i Phi Psi : term),
    spine_phi Sf i Phi Psi ->
    forall d k, spine_phi (lift d k Sf) (lift d k i) (lift d k Phi) (lift d k Psi).
Proof.
  intros Sf i Phi Psi H.
  induction H as
    [ Phi0 A Heval
    | Phi0 A c Phi' Psi' Heval Hsp IH
    | Phi0 A c Phi' Psi' Heval Hdesc Hsp IH
    | Phi0 Phin Heval Hneu ]; intros d k.
  - apply (@sph_nil (lift d k Sf) (lift d k i) (lift d k Phi0) (lift d k A)).
    exact (eval_lift_lnil_glm d k Phi0 A Heval).
  - apply (@sph_keep (lift d k Sf) (lift d k i) (lift d k Phi0)
                     (lift d k A) (lift d k c) (lift d k Phi') (lift d k Psi')).
    + exact (eval_lift_lcons_glm d k Phi0 A c Phi' Heval).
    + exact (IH d k).
  - apply (@sph_drop (lift d k Sf) (lift d k i) (lift d k Phi0)
                     (lift d k A) (lift d k c) (lift d k Phi') (lift d k Psi')).
    + exact (eval_lift_lcons_glm d k Phi0 A c Phi' Heval).
    + rewrite lift_branch_app_glm.
      exact (desc_against_lift_glm eval_lift_compat
               (TApp (branches (TApp Sf i)) c) Hdesc d k).
    + exact (IH d k).
  - apply (@sph_neutral (lift d k Sf) (lift d k i) (lift d k Phi0) (lift d k Phin)).
    + exact (eval_lift_compat d k Phi0 Phin Heval).
    + exact (neutral_lift_glm Phin Hneu d k).
Qed.

End SpinePhiLiftGlm.

Check spine_phi_lift_glm :
  eval_lift_compatible_glm ->
  forall Sf i Phi Psi : term,
    spine_phi Sf i Phi Psi ->
    forall d k, spine_phi (lift d k Sf) (lift d k i) (lift d k Phi) (lift d k Psi).
