Require Import Progress _tmp_epstep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma epbranches_nth_error : forall bs bs' k c b,
  epbranches bs bs' -> nth_error bs k = Some (c,b) ->
  exists c' b', nth_error bs' k = Some (c',b') /\ epstep c c' /\ epstep b b'.
Proof.
  intros bs bs' k c b Hbranches.
  revert k c b.
  induction Hbranches as [| x x' y y' bs bs' Hc Hb Htail IH].
  - intros k c b Hnth. destruct k; cbn in Hnth; discriminate.
  - intros k c0 b0 Hnth.
    destruct k as [|k].
    + cbn in Hnth. inversion Hnth; subst c0 b0.
      exists x', y'. repeat split; assumption.
    + cbn in Hnth.
      destruct (IH k c0 b0 Hnth) as [c0' [b0' [Hnth' [Hc0 Hb0]]]].
      exists c0', b0'. repeat split; assumption.
Qed.
