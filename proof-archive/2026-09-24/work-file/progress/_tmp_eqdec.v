Require Import Progress.
From Stdlib Require Import String.
From Stdlib Require Import PeanoNat.

Lemma term_eq_dec : forall x y : TypeRules.term, {x = y} + {x <> y}.
Proof.
  decide equality; try apply string_dec; try apply Nat.eq_dec.
  Show.
Abort.
