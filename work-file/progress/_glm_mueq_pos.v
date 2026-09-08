Require Import Progress.
Require Import _luna_mueq.
Require Import _luna_mueq_equiv.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma mueq_enum_pos_right_glm : forall c d n,
    enum_pos c n -> mueq c d -> d = c.
Proof.
  intros c d n Hpos. revert d. induction Hpos; intros d Hm; inversion Hm; subst;
    [reflexivity | f_equal; eapply IHHpos; eassumption].
Qed.

Lemma mueq_enum_pos_left_glm : forall c d n,
    enum_pos d n -> mueq c d -> c = d.
Proof.
  intros c d n Hpos Hmueq.
  apply (mueq_enum_pos_right_glm d c n Hpos).
  apply mueq_sym. exact Hmueq.
Qed.
