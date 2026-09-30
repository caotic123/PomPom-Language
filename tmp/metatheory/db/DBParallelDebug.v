From Stdlib Require Import List Arith Lia PeanoNat String.
Require Export ProofDB.DBParallelBase.
Import ListNotations.

Ltac db_congr :=
  solve [eassumption | apply pstep_refl |
    lazymatch goal with
    | |- pstep (lift ?d ?c ?t) (lift ?d ?c ?u) => apply pstep_lift; db_congr
    | |- pstep (subst ?a ?c ?t) (subst ?b ?c ?u) => apply pstep_subst; db_congr
    end | constructor; db_congr].
Ltac db_finish := cbn in *; repeat inv_known;
  solve [db_congr | apply_root ltac:(db_congr)].

Lemma pstep_complete : forall t u, pstep t u -> pstep u (pdev t).
Proof.
  intros t u H. induction H.
  all: try solve [db_finish].
  - destruct f; cbn [pdev]; try solve [apply ps_TApp; assumption]; db_finish.
  - destruct p; cbn [pdev]; try solve [apply ps_TFst; assumption]; db_finish.
  - destruct p; cbn [pdev]; try solve [apply ps_TSnd; assumption]; db_finish.
  - destruct E; cbn [pdev]; try solve [apply ps_TEPi; assumption]; db_finish.
  - destruct E; cbn [pdev]; try solve [apply ps_TSwitch; assumption].
    destruct p; cbn [pdev]; try solve [apply ps_TSwitch; assumption].
    destruct e; cbn [pdev]; try solve [apply ps_TSwitch; assumption].
    Show.
Abort.
