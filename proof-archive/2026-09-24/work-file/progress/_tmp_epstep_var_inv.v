Require Import Progress _tmp_epstep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma epstep_lift_var_inv : forall n k T,
  epstep (lift 1 k (TVar n)) T ->
  exists u, T = lift 1 k u /\ epstep (TVar n) u.
Proof.
  intros n k T H.
  cbn [lift] in H.
  destruct (Nat.ltb n k) eqn:Hlt; inversion H; subst T.
  - exists (TVar n). split; [cbn [lift]; rewrite Hlt; reflexivity | constructor].
  - exists (TVar n). split; [cbn [lift]; rewrite Hlt; reflexivity | constructor].
Qed.
