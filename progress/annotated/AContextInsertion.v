(* Removing an unused context slot. This is the context algebra needed by
   annotated strengthening; it makes no strengthening assumption. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AComparison.
Import ListNotations.

Inductive insertion : nat -> Raw.ctx -> Raw.ctx -> Prop :=
| insert_head : forall Gamma A, insertion 0 Gamma (A :: Gamma)
| insert_under : forall c Gamma Delta A,
    insertion c Gamma Delta ->
    insertion (S c) (A :: Gamma) (Raw.lift 1 c A :: Delta).

Lemma insertion_environment : forall c Gamma Delta,
  insertion c Gamma Delta -> RW.environment_lift c Gamma Delta.
Proof.
  intros c Gamma Delta H; induction H;
    auto using RW.environment_lift_head, RW.environment_lift_cons.
Qed.

Lemma insertion_length : forall c Gamma Delta,
  insertion c Gamma Delta -> List.length Delta = S (List.length Gamma).
Proof. intros c Gamma Delta H; induction H; cbn; congruence. Qed.

Lemma insertion_bound : forall c Gamma Delta,
  insertion c Gamma Delta -> c <= List.length Gamma.
Proof. intros c Gamma Delta H; induction H; cbn; lia. Qed.

Lemma insertion_lookup : forall c Gamma Delta,
  insertion c Gamma Delta -> forall n A,
  nth_error Delta (RW.shift_index c n) = Some A -> exists B,
  nth_error Gamma n = Some B /\
  Raw.lift 1 c (Raw.lift (S n) 0 B) =
    Raw.lift (S (RW.shift_index c n)) 0 A.
Proof.
  intros c Gamma Delta HI n A HA.
  assert (HN : RW.shift_index c n < List.length Delta).
  { apply nth_error_Some; rewrite HA; discriminate. }
  pose proof (insertion_length _ _ _ HI) as HL.
  pose proof (insertion_bound _ _ _ HI) as HB.
  assert (Hn : n < List.length Gamma).
  { unfold RW.shift_index in HN; destruct (n <? c) eqn:HC;
      apply Nat.ltb_lt in HC || apply Nat.ltb_ge in HC; lia. }
  destruct (nth_error Gamma n) as [B|] eqn:HE.
  - destruct (insertion_environment _ _ _ HI n B HE) as [C [HC HT]].
    rewrite HA in HC; inversion HC; subst C; eauto.
  - apply nth_error_Some in Hn; contradiction.
Qed.

Lemma comparison_unlift : forall A B c,
  RC.type_comparison (Raw.lift 1 c A) (Raw.lift 1 c B) ->
  RC.type_comparison A B.
Proof.
  intros A B c H.
  pose proof (RC.comparison_subst _ _ H Raw.TUnit c) as HS.
  now rewrite !RB.subst_lift_cancel in HS.
Qed.

Lemma recovered_typing : forall Gamma t T c,
  (exists S, typing Gamma t S /\
    RC.type_comparison (Raw.lift 1 c S) (Raw.lift 1 c T)) ->
  RT.type_wf Gamma T -> typing Gamma t T.
Proof.
  intros Gamma t T c [S [HS HC]] HT.
  eapply comparison_typing; [exact HS|now apply comparison_unlift in HC|exact HT].
Qed.

Lemma recovered_lower_typing : forall Gamma t T c,
  (exists S, typing Gamma t S /\ RC.type_comparison (Raw.lift 1 c S) T) ->
  RT.type_wf Gamma (Raw.subst Raw.TUnit c T) ->
  typing Gamma t (Raw.subst Raw.TUnit c T).
Proof.
  intros Gamma t T c [S [HS HC]] HT.
  pose proof (RC.comparison_subst _ _ HC Raw.TUnit c) as Hlower.
  rewrite RB.subst_lift_cancel in Hlower.
  eapply comparison_typing; eassumption.
Qed.

Print Assumptions insertion_lookup.
Print Assumptions recovered_typing.
