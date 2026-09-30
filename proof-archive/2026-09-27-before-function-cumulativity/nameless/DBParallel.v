From Stdlib Require Import List Arith Lia PeanoNat String.
Require Export nameless.DBInversion.
Import ListNotations.

Ltac db_congr :=
  solve [eassumption | apply pstep_refl |
    lazymatch goal with
    | |- pstep (lift ?d ?c ?t) (lift ?d ?c ?u) => apply pstep_lift; db_congr
    | |- pstep (subst ?a ?c ?t) (subst ?b ?c ?u) => apply pstep_subst; db_congr
    end | constructor; db_congr].
Ltac db_finish := cbn in *; repeat fast_inv;
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
    destruct e; cbn [pdev]; try solve [apply ps_TSwitch; assumption]; db_finish.
  - destruct D; cbn [pdev]; try solve [apply ps_TInterp; assumption]; db_finish.
  - destruct x; cbn [pdev]; try solve [apply ps_TInd; assumption]; db_finish.
  - destruct D; cbn [pdev]; try solve [apply ps_TIAll; assumption | db_finish].
    all: destruct x; cbn [pdev]; try solve [apply ps_TIAll; assumption]; db_finish.
  - destruct D; cbn [pdev]; try solve [apply ps_THyps; assumption | db_finish].
    all: destruct x; cbn [pdev]; try solve [apply ps_THyps; assumption]; db_finish.
  - destruct x; cbn [pdev]; try solve [apply ps_TCloseCase; assumption]; db_finish.
  - destruct x; cbn [pdev]; try solve [apply ps_TCloseInd; assumption]; db_finish.
Qed.

Lemma pstep_diamond : diamond pstep.
Proof.
  intros t u v Hu Hv. exists (pdev t).
  split; apply pstep_complete; assumption.
Qed.

Lemma pstep_confluent : confluent pstep.
Proof.
apply diamond_rtc_confluent, pstep_diamond. Qed.
