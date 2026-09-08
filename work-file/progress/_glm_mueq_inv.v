From Stdlib Require Import List.
Require Import _luna_mueq.
Import ListNotations TypeRules.

Lemma mueq_enumt_inv_glm : forall E E',
    mueq (TEnumT E) (TEnumT E') -> mueq E E'.
Proof.
  intros E E' H. inversion H; subst. assumption.
Qed.

Lemma mueq_pi_inv_glm : forall A A' B B',
    mueq (TPi A B) (TPi A' B') -> mueq A A' /\ mueq B B'.
Proof.
  intros A A' B B' H. inversion H; subst. split; assumption.
Qed.
