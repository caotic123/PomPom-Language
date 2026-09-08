(* Open obligation: an empty-label signature has no closed inhabitant. *)
Require Export TypeRulesCore.
From Stdlib Require Import List.
Import ListNotations.

Conjecture consistency_empty_sig : forall M Sf i A,
    check [] M (TApp (TMuS Sf) i) ->
    eval (labels (TApp Sf i)) (TLNil A) ->
    False.
