(* GLM worker 1 — the SPECIALIZED substitution fact needed by muapp_sort:    *)
(*                                                                           *)
(*   conv B (TSort j) -> forall a k, conv (subst a k B) (TSort j)            *)
(*                                                                           *)
(* plus the symmetric source form and a whd-HSort corollary.                *)
(*                                                                           *)
(* WHY the naive derivation induction is not enough, and what closes it.     *)
(* Inducting directly on `conv B (TSort j)` with the target frozen at a sort *)
(* fails at cv_trans: the first leg conv t u carries an arbitrary u, so no   *)
(* sort-IH exists for that leg.  The bridge is the closed skeleton-induction *)
(*   conv_subst_rigid_glm : conv u u' -> forall t k,                         *)
(*                            conv (subst u k t) (subst u' k t)             *)
(* (induction on the SKELETON t, never on conv — hence it needs no cv_phi    *)
(* residual at all).  With u = u' = a it transports the cv_trans first leg   *)
(* through the substitution.  Every remaining constructor is either          *)
(*   - cv_step / cv_refl / cv_sym : close directly,                          *)
(*   - cv_eta : substitution keeps the eta shape (subst_lift_one_zero),      *)
(*   - cv_phi or a congruence : its conclusion's second index is a           *)
(*     constructor application other than TSort, so the recognition premise  *)
(*     `v = TSort j` is discriminate-contradictory.                          *)
(* In particular a top-level cv_phi endpoint (whd HMuSApp) can never BE the  *)
(* sort target here: the derivation being inverted concludes at TSort j, and *)
(* cv_phi's conclusion concludes at TApp (TMuS _) _ — no uninversion needed. *)
(* No closure property of conv is assumed: the induction only uses the       *)
(* inductive definition of conv, closed facts about subst/step, and the      *)
(* closed rigid-transport theorem.                                           *)
(*                                                                           *)
(* General cutoff k is proved (k = 0 is the specialization).                *)

Require Import TypeRules Progress.
Require Import _glm_subst_reduction_bundle_step _glm_conv_subst_rigid.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(*  Step 1: recognition lemma — the sort target is stable under        *)
(*  substituting the SAME term a at cutoff k on both ends.             *)
(* ------------------------------------------------------------------ *)

Theorem conv_subst_sort_gen_glm :
  forall B v : term, conv B v ->
    forall j : nat, v = TSort j ->
      forall (a : term) (k : nat), conv (subst a k B) (TSort j).
Proof.
  intros B v H.
  induction H;
    intros j Heq a0 kk; cbn [subst] in *;
    try discriminate.
  - (* cv_step : the reduction transports (same a both sides); the target   *)
    (* is preserved by the IH on the step target u.                         *)
    eapply cv_trans.
    + apply cv_step. exact (step_subst_glm _ _ s a0 kk).
    + exact (IH j Heq a0 kk).
  - (* cv_refl : t = TSort j, and subst a k (TSort j) = TSort j. *)
    rewrite Heq. cbn [subst]. apply cv_refl.
  - (* cv_sym : flip the IH's equation. *)
    apply cv_sym. exact (IH j Heq a0 kk).
  - (* cv_trans : first leg by rigid skeleton transport (same a on both    *)
    (* sides — induction on the skeleton, no cv_phi residual needed),      *)
    (* second leg keeps the sort target by IH.                             *)
    eapply cv_trans.
    + exact (conv_subst_rigid_glm a0 a0 (cv_refl a0) t u kk).
    + exact (IH2 j Heq a0 kk).
  - (* cv_eta : substitution keeps the eta shape; here f = TSort j, and    *)
    (* lift 1 0 (TSort j) = TSort j, so cv_eta applies verbatim.           *)
    rewrite Heq. cbn [subst].
    rewrite subst_lift_one_zero. cbn [subst].
    apply (cv_eta (TSort j)).
Qed.

(* ------------------------------------------------------------------ *)
(*  Step 2: the main target theorem (general cutoff; k = 0 is the      *)
(*  specialization).                                                   *)
(* ------------------------------------------------------------------ *)

Theorem conv_subst_sort_target_glm :
  forall B j : term, conv B (TSort j) ->
    forall (a : term) (k : nat), conv (subst a k B) (TSort j).
Proof.
  intros B j H a k.
  exact (conv_subst_sort_gen_glm B (TSort j) H j eq_refl a k).
Qed.

(* ------------------------------------------------------------------ *)
(*  Step 3: symmetric source form.                                     *)
(* ------------------------------------------------------------------ *)

Theorem conv_subst_sort_source_glm :
  forall j B : term, conv (TSort j) B ->
    forall (a : term) (k : nat), conv (TSort j) (subst a k B).
Proof.
  intros j B H a k.
  apply cv_sym.
  exact (conv_subst_sort_gen_glm B (TSort j) (cv_sym H) j eq_refl a k).
Qed.

(* ------------------------------------------------------------------ *)
(*  Step 4: muapp_sort-shaped corollary — the target only needs to be  *)
(*  weak-head of class HSort, i.e. to evaluate to some TSort k0.       *)
(* ------------------------------------------------------------------ *)

Theorem conv_subst_sort_whd_glm :
  forall B U : term, conv B U -> whd U HSort ->
    forall (a : term) (k : nat), conv (subst a k B) U.
Proof.
  intros B U Hconv [u' [Hev Hshape]].
  inversion Hshape as [k0 Heq0 | | | | | | | | | | | |]; subst u'.
  pose proof (conv_of_eval U (TSort k0) Hev) as Hcu.
  eapply cv_trans; [ | exact (cv_sym Hcu) ].
  exact (conv_subst_sort_gen_glm B (TSort k0) (cv_trans Hconv Hcu) k0
           eq_refl a k).
Qed.

Print Assumptions conv_subst_sort_gen_glm.
Print Assumptions conv_subst_sort_target_glm.
Print Assumptions conv_subst_sort_source_glm.
Print Assumptions conv_subst_sort_whd_glm.
