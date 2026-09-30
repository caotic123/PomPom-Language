(* Multi-step preservation, derived from one-step preservation. *)
Require Export TypeRulesCore.
Require Import Preservation.
From Stdlib Require Import List.
Import ListNotations.

Lemma preservation_eval : forall Γ t t' A,
    check Γ t A -> eval t t' -> check Γ t' A.
Proof.
  intros Γ t t' A Ht Hev. revert Ht. induction Hev; intro Ht.
  - exact Ht.
  - apply IHHev. eapply preservation; eauto.
Qed.
