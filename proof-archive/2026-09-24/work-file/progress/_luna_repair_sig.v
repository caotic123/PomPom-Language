Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.

(* The pruning constructor itself can erase a member.  This is the exact
   transport obstruction for a check derivation passing through ch_expand. *)
Lemma spine_phi_drop_member_obstruction : forall Sf i Phi A c Phi',
    eval Phi (TLCons A c Phi') ->
    desc_against (TApp (branches (TApp Sf i)) c) ->
    spine_phi Sf i Phi Phi' ->
    spine_mem c Phi.
Proof.
  intros Sf i Phi A c Phi' Heval Hdead Htail.
  apply sm_here with (A := A) (c' := c) (Phi' := Phi').
  - exact Heval.
  - apply cv_refl.
Qed.

Lemma spine_phi_drop_target_can_be_empty : forall Sf i Phi A c Phi',
    eval Phi (TLCons A c Phi') ->
    desc_against (TApp (branches (TApp Sf i)) c) ->
    spine_phi Sf i Phi Phi' ->
    forall q, ~ spine_mem q (TLNil A).
Proof.
  intros Sf i Phi A c Phi' Heval Hdead Htail q Hmem.
  change (spine_mem q (TLNil A)) in Hmem.
  inversion Hmem; subst.
  all: match goal with
       | Hx : eval (TLNil _) _ |- _ =>
           pose proof (eval_tlnil_refl _ _ Hx) as K; discriminate K
       end.
Qed.

Print Assumptions spine_phi_drop_member_obstruction.
Print Assumptions spine_phi_drop_target_can_be_empty.
