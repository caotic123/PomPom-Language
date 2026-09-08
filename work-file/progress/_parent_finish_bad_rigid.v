Require Import Progress _tmp_epstep _work_mixed_closure _luna_finish_eta_sort.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

Lemma lift1_not_var0 : forall g, lift 1 0 g <> TVar 0.
Proof. intros g H; destruct g; cbn [lift] in H; discriminate. Qed.
Lemma lift1_not_mus_var0 : forall g, lift 1 0 g <> TMuS (TVar 0).
Proof.
  intros g H; destruct g; cbn [lift] in H; try discriminate.
  injection H. apply lift1_not_var0.
Qed.
Lemma lift1_not_bad_pair : forall f,
  lift 1 0 f <> TPair (TMuS (TVar 0)) (TSort 0).
Proof.
  intros f H; destruct f; cbn [lift] in H; try discriminate.
  injection H. intros _ Hbad. eapply lift1_not_mus_var0; exact Hbad.
Qed.
Lemma bad_epstep_id_parent : forall u, epstep bad_t u -> u = bad_t.
Proof.
  intros u H. unfold bad_t in *.
  inversion H; subst; clear H.
  match goal with H : epstep (TLam _) _ |- _ => inversion H; subst; clear H end.
  - repeat match goal with
    | H : epstep (TApp _ _) _ |- _ => inversion H; subst; clear H
    | H : epstep (TPair _ _) _ |- _ => inversion H; subst; clear H
    | H : epstep (TMuS _) _ |- _ => inversion H; subst; clear H
    | H : epstep (TVar _) _ |- _ => inversion H; subst; clear H
    | H : epstep (TSort _) _ |- _ => inversion H; subst; clear H
    end. reflexivity.
  - exfalso. match goal with
    | H : TPair _ _ = lift 1 0 ?f |- _ => exact (lift1_not_bad_pair f (eq_sym H))
    | H : lift 1 0 ?f = TPair _ _ |- _ => exact (lift1_not_bad_pair f H)
    end.
Qed.
Print Assumptions bad_epstep_id_parent.
