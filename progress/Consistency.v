(* Open obligation: bottom has no closed inhabitant. *)
Require Export TypeRulesCore.
From Stdlib Require Import List.
Import ListNotations.

Conjecture consistency : forall t, ~ check [] t Bot.
