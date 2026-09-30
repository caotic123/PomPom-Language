(* GLM worker 4 — conv_subst0: the exact small theorem at cutoff 0, proved   *)
(* by the beta-expansion bridge (no induction on conv, no cv_phi case).     *)
(*                                                                          *)
(*   conv_subst0_glm :                                                      *)
(*     forall t t' a a',                                                    *)
(*       conv t t' -> conv a a' ->                                          *)
(*       conv (subst a 0 t) (subst a' 0 t').                                *)
(*                                                                          *)
(* Architecture: expand both sides back to their redexes and use conv's     *)
(* congruence in the middle:                                                *)
(*                                                                          *)
(*   subst a 0 t                                                            *)
(*     <-beta-  TApp (TLam t) a        (st_beta : TApp (TLam t) a ↦ subst a 0 t) *)
(*     -congr-> TApp (TLam t') a'      (cv_lam on conv t t', cv_app)        *)
(*     -beta->  subst a' 0 t'          (st_beta again, forward)             *)
(*                                                                          *)
(* chained with cv_sym + cv_trans.  Because conv is the smallest congruence *)
(* containing beta (cv_step), the bridge uses only cv_step, cv_app, cv_lam, *)
(* cv_sym, cv_trans — so the cv_phi pruning rule never enters the picture.  *)

Require Import TypeRules Progress.

From Stdlib Require Import List Arith Lia.

(* The exact target statement (verbatim from the task). *)
Theorem conv_subst0_glm :
  forall t t' a a',
    conv t t' -> conv a a' ->
    conv (subst a 0 t) (subst a' 0 t').
Proof.
  intros t t' a a' Ht Ha.
  (* Left leg: subst a 0 t  <-beta-  TApp (TLam t) a. *)
  eapply cv_trans.
  - apply cv_sym.
    apply cv_step.
    apply st_beta.
  (* Middle: congruence through the application, expanding t and a. *)
  - eapply cv_trans.
    + apply cv_app.
      * apply cv_lam.
        exact Ht.
      * exact Ha.
    (* Right leg: TApp (TLam t') a'  -beta->  subst a' 0 t'. *)
    + apply cv_step.
      apply st_beta.
Qed.

(* Corollary 1 — same substituent: converting the substituted term alone    *)
(* suffices when the substituent is literally identical.                    *)
Corollary conv_subst0_same_subst_glm :
  forall t t' a,
    conv t t' ->
    conv (subst a 0 t) (subst a 0 t').
Proof.
  intros t t' a Ht.
  apply (conv_subst0_glm t t' a a).
  - exact Ht.
  - apply cv_refl.
Qed.

(* Corollary 2 — sort target at cutoff 0: substituting a sort as the        *)
(* substituent transports conversion of the body.  (The substituent being   *)
(* TSort s makes this the exact instance used for type-level substitution.) *)
Corollary conv_subst0_sort_target_glm :
  forall s t t',
    conv t t' ->
    conv (subst (TSort s) 0 t) (subst (TSort s) 0 t').
Proof.
  intros s t t' Ht.
  apply conv_subst0_same_subst_glm.
  exact Ht.
Qed.

Print Assumptions conv_subst0_glm.
Print Assumptions conv_subst0_same_subst_glm.
Print Assumptions conv_subst0_sort_target_glm.
