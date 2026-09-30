(* Formation information retained by checking a syntactic Pi. *)

Require Import Progress.
From Stdlib Require Import List.
Import ListNotations TypeRules.

Lemma check_pi_formation_parent : forall G t T,
    check G t T ->
    forall A B, t = TPi A B ->
      exists k,
        check G A (TSort k) /\ check (A :: G) B (TSort k).
Proof.
  intros G t T Hck.
  induction Hck; intros A0 B0 Ht; subst; try discriminate.
  - inversion H; subst.
    eexists. split; eassumption.
  - inversion H; subst.
    eexists. split; eassumption.
  - eapply IHHck. reflexivity.
Qed.

Print Assumptions check_pi_formation_parent.
