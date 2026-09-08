(* Open obligation: closed typed terms evaluate to weak-head values. *)
Require Export TypeRulesCore.
From Stdlib Require Import List.
Import ListNotations.

Conjecture normalization : forall t A,
    check [] t A -> exists v, eval t v /\ value v.
