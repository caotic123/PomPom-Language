Require Import Progress.
Import TypeRules.

Lemma enum_pos_lift_inv_luna : forall c n d k,
    enum_pos (lift d k c) n -> enum_pos c n.
Proof.
  intros c n d k. revert n.
  induction c; intros n0 H; cbn [lift] in H;
    try solve [destruct (Nat.ltb _ _) eqn:Hl; cbn in H; inversion H];
    try inversion H.
  - inversion H; constructor.
  - inversion H; subst. constructor. apply IHc. assumption.
Qed.
