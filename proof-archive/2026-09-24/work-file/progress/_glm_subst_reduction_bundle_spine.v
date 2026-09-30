(* GLM worker 1 — spine_phi is stable under same-substituent substitution:   *)
(* Sf, i, Phi and Psi are all substituted by the SAME u at the SAME cutoff k. *)
(*                                                                            *)
(* Uses eval_subst_glm (via _glm_subst_reduction_bundle_eval) for the eval    *)
(* premises, desc_against_subst_glm for the pruning witness, and             *)
(* neutral_subst_glm for the neutral tail — hence the `neutral u` premise.   *)

Require Import TypeRules Progress.
Require Import _glm_subst_reduction_bundle_step _glm_subst_reduction_bundle_eval
               _glm_subst_reduction_bundle_sem.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* branches (TApp Sf i) commutes with substitution — definitional, since     *)
(* branches is TFst and TFst (TApp Sf i) is a constructor application.       *)
Lemma subst_branch_app_glm : forall (u : term) (k : nat) (Sf i c : term),
  TApp (branches (TApp (subst u k Sf) (subst u k i))) (subst u k c) =
  subst u k (TApp (branches (TApp Sf i)) c).
Proof.
  intros u k Sf i c. reflexivity.
Qed.

Theorem spine_phi_subst_glm :
  forall (Sf i Phi Psi : term),
    spine_phi Sf i Phi Psi ->
    forall (u : term) (k : nat),
      neutral u ->
      spine_phi (subst u k Sf) (subst u k i) (subst u k Phi) (subst u k Psi).
Proof.
  intros Sf i Phi Psi H.
  induction H as
    [ Phi0 A Heval
    | Phi0 A c Phi' Psi' Heval Hsp IH
    | Phi0 A c Phi' Psi' Heval Hdesc Hsp IH
    | Phi0 Phin Heval Hneu ]; intros u k Hu.
  - (* sph_nil *)
    apply (@sph_nil (subst u k Sf) (subst u k i)
                    (subst u k Phi0) (subst u k A)).
    exact (eval_subst_glm _ _ Heval u k).
  - (* sph_keep *)
    apply (@sph_keep (subst u k Sf) (subst u k i) (subst u k Phi0)
                     (subst u k A) (subst u k c) (subst u k Phi')
                     (subst u k Psi')).
    + exact (eval_subst_glm _ _ Heval u k).
    + exact (IH u k Hu).
  - (* sph_drop *)
    apply (@sph_drop (subst u k Sf) (subst u k i) (subst u k Phi0)
                     (subst u k A) (subst u k c) (subst u k Phi')
                     (subst u k Psi')).
    + exact (eval_subst_glm _ _ Heval u k).
    + rewrite subst_branch_app_glm.
      exact (desc_against_subst_glm _ Hdesc u k).
    + exact (IH u k Hu).
  - (* sph_neutral *)
    apply (@sph_neutral (subst u k Sf) (subst u k i)
                        (subst u k Phi0) (subst u k Phin)).
    + exact (eval_subst_glm _ _ Heval u k).
    + exact (neutral_subst_glm _ Hneu u k Hu).
Qed.

Check spine_phi_subst_glm :
  forall Sf i Phi Psi : term,
    spine_phi Sf i Phi Psi ->
    forall (u : term) (k : nat),
      neutral u ->
      spine_phi (subst u k Sf) (subst u k i) (subst u k Phi) (subst u k Psi).
