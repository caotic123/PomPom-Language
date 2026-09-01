From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules.

Inductive rtc' {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
| rtc'_refl : forall x, rtc' R x x
| rtc'_step : forall x y z, R x y -> rtc' R y z -> rtc' R x z.

Lemma pos_step_normal' : forall c n, enum_pos c n -> forall c', ~ step c c'.
Proof.
  intros c n H. induction H; intros c' Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IHenum_pos; eauto.
Qed.

Lemma enum_pos_functional' : forall c n m,
    enum_pos c n -> enum_pos c m -> n = m.
Proof.
  intros c n m Hn. revert m. induction Hn; intros m Hm.
  - inversion Hm. reflexivity.
  - inversion Hm; subst. f_equal. eapply IHHn. assumption.
Qed.

Lemma eval_enum_pos_refl' : forall c n v,
    enum_pos c n -> eval c v -> v = c.
Proof.
  intros c n v Hp He. inversion He; subst; [reflexivity |].
  exfalso. eapply pos_step_normal'; eassumption.
Qed.

Parameter conv_join : forall t u, conv t u -> exists v, eval t v /\ eval u v.

Lemma conv_pos_join' : forall c d n m,
    conv c d -> enum_pos c n -> enum_pos d m -> n = m.
Proof.
  intros c d n m Hcd Hc Hd.
  destruct (conv_join c d Hcd) as [v [Hcv Hdv]].
  pose proof (eval_enum_pos_refl' c n v Hc Hcv) as Ec.
  pose proof (eval_enum_pos_refl' d m v Hd Hdv) as Ed.
  subst v. subst d.
  eapply enum_pos_functional'; eassumption.
Qed.
