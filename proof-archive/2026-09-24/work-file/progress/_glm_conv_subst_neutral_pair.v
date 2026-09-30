(* GLM worker 1 — conv-subst layer 3: the two-sided theorem closed under     *)
(* substituents that are (convertible to) neutrals.                          *)
(*                                                                          *)
(*   conv_subst_neutral_pair_glm : conv t t' -> conv u u' ->                *)
(*       neutral u -> neutral u' -> forall k,                               *)
(*         conv (subst u k t) (subst u' k t')                               *)
(*                                                                          *)
(* Decomposition (no neutrality needed in the second leg):                  *)
(*   conv (subst u k t) (subst u k t')   -- conv_subst_same_neutral_glm     *)
(*   conv (subst u k t') (subst u' k t') -- conv_subst_rigid_glm            *)
(*   joined by cv_trans.                                                    *)
(*                                                                          *)
(* The neutrality hypothesis can be weakened: it suffices that ONE side of  *)
(* the substituent pair is convertible to some neutral n — then conv u' n   *)
(* follows by cv_sym/cv_trans, and the same three-leg chain runs with n as  *)
(* the pivot substituent.                                                   *)

Require Import TypeRules Progress.
Require Import _glm_conv_subst_rigid _glm_conv_subst_same_neutral.

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Theorem conv_subst_neutral_pair_glm :
  forall t t' u u' : term, conv t t' -> conv u u' ->
    neutral u -> neutral u' ->
    forall k : nat, conv (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' Ht Hu Hunat Hunat' k.
  eapply cv_trans.
  + exact (conv_subst_same_neutral_glm t t' Ht u Hunat k).
  + exact (conv_subst_rigid_glm u u' Hu t' k).
Qed.

(* Weakest usable hypothesis so far: one side convertible to a neutral.     *)
(*   conv t t' -> conv u u' -> (exists n, neutral n /\ conv u n)             *)
(*   -> forall k, conv (subst u k t) (subst u' k t')                         *)
(* Pivot: subst n k on the middle leg; the outer legs are rigid swaps.      *)
Theorem conv_subst_one_neutral_glm :
  forall t t' u u' : term, conv t t' -> conv u u' ->
    (exists n : term, neutral n /\ conv u n) ->
    forall k : nat, conv (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' Ht Hu [n [Hn Hnconv]].
  assert (Hn'u' : conv n u').
  { eapply cv_trans.
    - apply cv_sym. exact Hnconv.
    - exact Hu. }
  intros k.
  eapply cv_trans.
  - exact (conv_subst_rigid_glm u n Hnconv t k).
  - eapply cv_trans.
    + exact (conv_subst_same_neutral_glm t t' Ht n Hn k).
    + exact (conv_subst_rigid_glm n u' Hn'u' t' k).
Qed.
