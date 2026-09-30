Require Import TypeRules Progress.

Theorem neutral_lift_glm : forall t, neutral t -> forall d k, neutral (lift d k t).
Proof.
  intros t H; induction H; intros d k; simpl.
  - simpl; destruct (PeanoNat.Nat.ltb n k); apply ne_var.
  - apply ne_app; auto.
  - apply ne_fst; auto.
  - apply ne_snd; auto.
  - apply ne_switch; auto.
  - apply ne_ind; auto.
  - apply ne_case; auto.
Qed.
