(* Open obligation: the empty enumeration has no closed inhabitant. *)
Require Export TypeRulesCore.
From Stdlib Require Import List.
Import ListNotations.

Conjecture consistency_enum : forall t, ~ check [] t (TEnumT TNilE).
