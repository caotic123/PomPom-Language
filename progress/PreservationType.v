(* Proved: reducing a type preserves checking at that type. *)
Require Export TypeRulesCore.
From Stdlib Require Import List.
Import ListNotations.

Lemma preservation_type : forall Γ t A A',
    check Γ t A -> step A A' -> check Γ t A'.
Proof.
  intros Γ t A A' Ht Hst. eapply ch_expand.
  - apply cv_sym. eapply cv_step. exact Hst.
  - exact Ht.
Qed.
