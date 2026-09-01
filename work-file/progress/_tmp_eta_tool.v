Require Import Progress _tmp_epstep _tmp_epstep_inv.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma eta_app_inv : forall f t,
  epstep (TApp (lift 1 0 f) (TVar 0)) t ->
  exists u, t = TApp (lift 1 0 u) (TVar 0) /\ epstep f u.
Proof.
  intros f t H.
  inversion H; subst.
  inversion H4; subst a'.
  destruct (epstep_lift_inv f 0 f' H2) as [u [Hu Hfu]].
  exists u. split; [rewrite Hu; reflexivity | exact Hfu].
Qed.
