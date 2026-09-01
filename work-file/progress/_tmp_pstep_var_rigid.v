Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma pstep_var_rigid : forall n t, pstep (TVar n) t -> t = TVar n.
Proof.
  intros n t H.
  inversion H; reflexivity.
Qed.
