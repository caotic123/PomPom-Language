Require Import _luna_mueq _luna_mueq_equiv.
From Stdlib Require Import List.

Lemma mubeq_nth_error_fwd :
  forall bs bs', mubeq bs bs' ->
    forall k x y, nth_error bs k = Some (x, y) ->
    exists x' y', nth_error bs' k = Some (x', y') /\ mueq x x' /\ mueq y y'.
Proof.
  intros bs bs' H. induction H; intros k x y Hnth.
  - destruct k; simpl in Hnth; discriminate.
  - destruct k as [|k]; simpl in Hnth.
    + injection Hnth as Hx Hy; subst.
      exists c', b'. repeat split; assumption.
    + destruct (IHmubeq k x y Hnth) as [x0 [y0 [Hnth' [Hx Hy]]]].
      exists x0, y0. repeat split; assumption.
Qed.

Lemma mubeq_nth_error_bwd :
  forall bs bs', mubeq bs bs' ->
    forall k x' y', nth_error bs' k = Some (x', y') ->
    exists x y, nth_error bs k = Some (x, y) /\ mueq x x' /\ mueq y y'.
Proof.
  intros bs bs' H.
  apply mubeq_sym in H.
  intros k x y Hnth.
  destruct (mubeq_nth_error_fwd bs' bs H k x y Hnth) as [x0 [y0 [Hnth' [Hx Hy]]]].
  exists x0, y0. repeat split; auto using mueq_sym.
Qed.
