(* Open obligation: canonical forms for well-formed signature instances.
   The index-typing premise is essential and is preserved here. *)
Require Export TypeRulesCore.
From Stdlib Require Import List.
Import ListNotations.

Conjecture canonical_forms_sig : forall M Sf i IT E,
    check [] IT (TSort 0) -> check [] E TEnumU ->
    check [] Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) ->
    check [] i IT ->
    check [] M (TApp (TMuS Sf) i) ->
    exists c xs Phi,
      eval M (TIn (TPair c xs)) /\
      eval (labels (TApp Sf i)) Phi /\
      spine_mem c Phi /\
      check [] xs (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)).
