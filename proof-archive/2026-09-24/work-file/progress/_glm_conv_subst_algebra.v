(* GLM worker 1 — conv-subst algebra: the substitution/lift commutations     *)
(* needed to transport the eta rule and the cv_phi branch-family premise     *)
(* through same-cutoff substitution.                                         *)
(*                                                                           *)
(*   subst_lift_one_zero (Progress.v): subst u (S k) (lift 1 0 t)            *)
(*                                     = lift 1 0 (subst u k t)              *)
(* handles cv_eta directly (there the IH lives at cutoff S k and the eta     *)
(* shape is re-exposed at the substituted f).  For cv_phi the same equation  *)
(* transports the branch-family premise: substituting at cutoff S k into     *)
(* TLam (branches (TApp (lift 1 0 S) (TVar 0))) yields the eta shape of the  *)
(* substituted S at cutoff k — the substitution twin of eta_branch_lift in   *)
(* _glm_conv_lift_bundle_main.v.                                             *)

Require Import TypeRules Progress.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* Substitution into the cv_phi branch-family shape keeps the eta form, with *)
(* the substituted S at the same cutoff: under the TLam binder the cutoff    *)
(* becomes S k, and subst_lift_one_zero at S k maps back down to k — so the  *)
(* equation holds for every k (the bound TVar 0 satisfies 0 < S k).          *)
(*   subst u k (TLam (branches (TApp (lift 1 0 S) (TVar 0))))                *)
(*   = TLam (branches (TApp (lift 1 0 (subst u k S)) (TVar 0)))              *)
Lemma subst_eta_branch_glm : forall (S0 u : term) (k : nat),
    subst u k (TLam (branches (TApp (lift 1 0 S0) (TVar 0)))) =
    TLam (branches (TApp (lift 1 0 (subst u k S0)) (TVar 0))).
Proof.
  intros S0 u k. cbn [subst branches].
  rewrite subst_lift_one_zero. reflexivity.
Qed.

(* Same for the bare cv_eta shape:                                          *)
(*   subst u k (TLam (TApp (lift 1 0 f) (TVar 0)))                          *)
(*   = TLam (TApp (lift 1 0 (subst u k f)) (TVar 0))                        *)
Lemma subst_eta_shape_glm : forall (f u : term) (k : nat),
    subst u k (TLam (TApp (lift 1 0 f) (TVar 0))) =
    TLam (TApp (lift 1 0 (subst u k f)) (TVar 0)).
Proof.
  intros f u k. cbn [subst].
  rewrite subst_lift_one_zero. reflexivity.
Qed.

(* Twin for lifting (re-exposes the eta shape after lifting):                *)
(*   lift d k (TLam (branches (TApp (lift 1 0 S) (TVar 0))))                 *)
(*   = TLam (branches (TApp (lift 1 0 (lift d k S)) (TVar 0)))               *)
Lemma eta_branch_lift_glm : forall (S0 : term) (d k : nat),
    lift d k (TLam (branches (TApp (lift 1 0 S0) (TVar 0)))) =
    TLam (branches (TApp (lift 1 0 (lift d k S0)) (TVar 0))).
Proof.
  intros S0 d k. cbn [lift branches].
  rewrite lift_lift_one_zero. reflexivity.
Qed.

Check subst_eta_branch_glm :
  forall S0 u : term, forall k : nat,
    subst u k (TLam (branches (TApp (lift 1 0 S0) (TVar 0)))) =
    TLam (branches (TApp (lift 1 0 (subst u k S0)) (TVar 0))).
Check subst_eta_shape_glm :
  forall f u : term, forall k : nat,
    subst u k (TLam (TApp (lift 1 0 f) (TVar 0))) =
    TLam (TApp (lift 1 0 (subst u k f)) (TVar 0)).
Check eta_branch_lift_glm :
  forall S0 : term, forall d k : nat,
    lift d k (TLam (branches (TApp (lift 1 0 S0) (TVar 0)))) =
    TLam (branches (TApp (lift 1 0 (lift d k S0)) (TVar 0))).
