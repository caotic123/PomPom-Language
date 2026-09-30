(* Inversion retains the actual annotations through arbitrary conversion
   and function/universe cumulativity chains. *)
From Stdlib Require Import List Arith.
Require Export annotated.AComparison.
Import ListNotations.
Module RCore := nameless.DBCore.

Lemma lambda_generation : forall Gamma t T, typing Gamma t T -> forall A B b,
  t = TLam A B b -> exists j k,
  typing Gamma A (Raw.TSort j) /\
  typing (erase A :: Gamma) B (Raw.TSort k) /\
  typing (erase A :: Gamma) b (erase B) /\
  RC.type_comparison (Raw.TPi (erase A) (erase B)) T.
Proof.
  intros Gamma t T H; induction H; intros AA BB body HE; try discriminate.
  - inversion HE; subst; exists j, k; repeat split; try assumption.
    apply RC.cmp_conversion, RCore.cv_refl.
  - destruct (IHtyping _ _ _ HE) as [j [l [HA [HB [Ht HC]]]]].
    exists j, l; repeat split; try assumption.
    eapply RC.comparison_right_conversion; eassumption.
  - destruct (IHtyping _ _ _ HE) as [l [m [HA [HB [Ht HC]]]]].
    exists l, m; repeat split; try assumption.
    eapply RC.comparison_transitive; [exact HC|].
    apply RC.comparison_universe, RT.ul_sort; assumption.
  - destruct (IHtyping _ _ _ HE) as [l [m [HA [HB [Ht HC]]]]].
    exists l, m; repeat split; try assumption.
    eapply RC.comparison_transitive; [exact HC|].
    apply RC.comparison_universe, RT.ul_pi; assumption.
Qed.

Lemma application_generation : forall Gamma t T, typing Gamma t T -> forall A B f a,
  t = TApp A B f a -> exists j k,
  typing Gamma A (Raw.TSort j) /\
  typing (erase A :: Gamma) B (Raw.TSort k) /\
  typing Gamma f (Raw.TPi (erase A) (erase B)) /\
  typing Gamma a (erase A) /\
  RC.type_comparison (Raw.subst (erase a) 0 (erase B)) T.
Proof.
  intros Gamma t T H; induction H; intros AA BB fn arg HE; try discriminate.
  - inversion HE; subst; exists j, k; repeat split; try assumption.
    apply RC.cmp_conversion, RCore.cv_refl.
  - destruct (IHtyping _ _ _ _ HE) as [j [l [HA [HB [Hf [Ha HC]]]]]].
    exists j, l; repeat split; try assumption.
    eapply RC.comparison_right_conversion; eassumption.
  - destruct (IHtyping _ _ _ _ HE) as [l [m [HA [HB [Hf [Ha HC]]]]]].
    exists l, m; repeat split; try assumption.
    eapply RC.comparison_transitive; [exact HC|].
    apply RC.comparison_universe, RT.ul_sort; assumption.
  - destruct (IHtyping _ _ _ _ HE) as [l [m [HA [HB [Hf [Ha HC]]]]]].
    exists l, m; repeat split; try assumption.
    eapply RC.comparison_transitive; [exact HC|].
    apply RC.comparison_universe, RT.ul_pi; assumption.
Qed.

Print Assumptions lambda_generation.
Print Assumptions application_generation.
