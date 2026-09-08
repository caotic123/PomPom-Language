(* Small syntax lemmas used by the sort-ending erasure proofs. *)

Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma phi_erase_sort_preimage_parent : forall t j,
    phi_erase t = TSort j -> t = TSort j.
Proof.
  destruct t; cbn; intros j H; try discriminate.
  now inversion H.
Qed.

Lemma phi_erase_var_preimage_parent : forall t index,
    phi_erase t = TVar index -> t = TVar index.
Proof.
  destruct t; cbn; intros index H; try discriminate.
  now inversion H.
Qed.

Lemma subst0_sort_preimage_parent : forall u t j,
    subst u 0 t = TSort j ->
    t = TSort j \/ (t = TVar 0 /\ u = TSort j).
Proof.
  intros u t j H.
  destruct t; cbn in H; try discriminate.
  - destruct n as [|n]; cbn in H.
    + right. split; [reflexivity |].
      destruct u; cbn in H; try discriminate.
      now inversion H.
    + discriminate.
  - left. now inversion H.
Qed.

Lemma phi_erase_enum_pos_reflect_parent : forall t n,
    enum_pos (phi_erase t) n -> enum_pos t n.
Proof.
  intros t n H.
  remember (phi_erase t) as e eqn:He.
  revert t He.
  induction H; intros t He; destruct t; cbn in He; try discriminate.
  - constructor.
  - inversion He; subst. constructor. eapply IHenum_pos; reflexivity.
Qed.

Print Assumptions subst0_sort_preimage_parent.
Print Assumptions phi_erase_enum_pos_reflect_parent.
