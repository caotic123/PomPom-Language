Require Import Progress _work_cjoin _work_cstep_invariants
  _luna_phi_erase_shapes.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma conv_enumt_hshape_luna : forall E1 E2 h1 h2,
    conv (TEnumT E1) (TEnumT E2) ->
    hshape E1 h1 -> hshape E2 h2 -> h1 = h2.
Proof.
  intros E1 E2 h1 h2 Hconv Hshape1 Hshape2.
  destruct (conv_phi_cjoin _ _ Hconv)
    as [w [Hleft Hright]].
  destruct (rtc_cstep_enumt_inv (phi_erase E1) w Hleft)
    as [W1 [Hw1 Hinner1]].
  destruct (rtc_cstep_enumt_inv (phi_erase E2) w Hright)
    as [W2 [Hw2 Hinner2]].
  rewrite Hw1 in Hw2.
  inversion Hw2; subst W2.
  apply (hshape_tag_unique W1 h1 h2).
  - apply rtc_cstep_hshape with (t := phi_erase E1).
    + exact Hinner1.
    + apply phi_erase_hshape_luna. exact Hshape1.
  - apply rtc_cstep_hshape with (t := phi_erase E2).
    + exact Hinner2.
    + apply phi_erase_hshape_luna. exact Hshape2.
Qed.
