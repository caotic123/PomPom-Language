(* Full preservation for the annotated core.

   [reduction] is the complete annotated reduction relation: every primitive
   root computation, general eta contraction without a value, neutral, or
   reduct-typing restriction, and every one-hole compatible context, including
   binders and all annotations. The statement has exactly the shape of the
   refuted named proposition [full_preservation_statement]. *)
Require Export annotated.AStructuralPreservation.
Module RCore := nameless.DBCore.

Definition reduction := structural_step.

Inductive reduces : term -> term -> Prop :=
| reduces_refl : forall t, reduces t t
| reduces_step : forall t u v, reduction t u -> reduces u v -> reduces t v.

Theorem full_preservation : forall Gamma t u A,
  typing Gamma t A -> reduction t u -> typing Gamma u A.
Proof.
  intros Gamma t u A HT HR; exact (structural_step_preservation _ _ HR _ _ HT).
Qed.

Theorem full_preservation_reduces : forall Gamma t u A,
  typing Gamma t A -> reduces t u -> typing Gamma u A.
Proof.
  intros Gamma t u A HT HR; revert HT; induction HR; eauto using full_preservation.
Qed.

(* Each annotated step is a raw step of its erasure, or a step inside an
   annotation that erasure removes. *)
#[local] Hint Constructors RCore.reduction : raw_reduction.

Theorem reduction_erasure : forall t u, reduction t u ->
  erase t = erase u \/ RCore.reduction (erase t) (erase u).
Proof.
  fix IH 3; intros t u H; destruct H.
  - right; apply structural_root_erasure; assumption.
  - right; apply eta_root_erasure; assumption.
  - destruct H; cbn [erase]; try (left; reflexivity);
      match goal with HR : structural_step _ _ |- _ =>
        destruct (IH _ _ HR) as [HE|HE]
      end;
      solve [left; rewrite HE; reflexivity | right; eauto 2 with raw_reduction].
Qed.

Corollary reduces_erasure : forall t u, reduces t u ->
  RCore.reduces (erase t) (erase u).
Proof.
  intros t u H; induction H; [constructor|].
  destruct (reduction_erasure _ _ H) as [HE|HE];
    [rewrite HE; assumption|econstructor; eassumption].
Qed.

Print Assumptions full_preservation.
Print Assumptions full_preservation_reduces.
Print Assumptions reduction_erasure.
