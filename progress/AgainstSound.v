(* Open obligation: impossibility of well-typed descriptions implies
   that their interpreted payload types have no closed inhabitant. *)
Require Export TypeRulesCore.
From Stdlib Require Import List.
Import ListNotations.

Conjecture against_sound : forall IT D X t,
    check [] IT (TSort 0) ->
    check [] D (TIDesc IT) ->
    check [] X (TPi IT (TSort 0)) ->
    desc_against D ->
    ~ check [] t (TInterp D X).
