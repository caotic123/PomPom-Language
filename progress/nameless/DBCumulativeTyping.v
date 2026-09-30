(* Checked chains of conversion and universe comparison. Recording formation
   makes intermediate types available when a chain is lifted through Pi. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBGeneration.
Import ListNotations.

Inductive type_change (Gamma : ctx) : term -> term -> Prop :=
| tc_conversion : forall A B,
    type_wf Gamma A -> type_wf Gamma B -> conv A B -> type_change Gamma A B
| tc_universe : forall A B,
    type_wf Gamma A -> type_wf Gamma B -> universe_le A B -> type_change Gamma A B
| tc_transitive : forall A B C,
    type_change Gamma A B -> type_change Gamma B C -> type_change Gamma A C.

Lemma type_change_refl : forall Gamma A,
  type_wf Gamma A -> type_change Gamma A A.
Proof. intros; apply tc_conversion; auto using cv_refl. Qed.

Lemma type_change_formation : forall Gamma A B,
  type_change Gamma A B -> type_wf Gamma A /\ type_wf Gamma B.
Proof. intros Gamma A B H; induction H; intuition. Qed.

Theorem type_change_typing : forall Gamma A B,
  type_change Gamma A B -> forall t, typing Gamma t A -> typing Gamma t B.
Proof.
  intros Gamma A B H; induction H; intros t Ht.
  - destruct H0 as [k HB]; eapply ty_conv; eassumption.
  - eapply universe_le_typing; eassumption.
  - auto.
Qed.

Theorem type_change_narrowing : forall Gamma A B,
  type_change Gamma A B -> forall t T,
  typing (B::Gamma) t T -> typing (A::Gamma) t T.
Proof.
  intros Gamma A B H; induction H; intros t T Ht.
  - destruct H as [j HA], H0 as [k HB].
    eapply context_conversion; [exact HB|exact HA|now apply cv_sym|exact Ht].
  - destruct H as [j HA], H0 as [k HB].
    eapply context_narrowing; [exact HB|exact HA|exact H1|exact Ht].
  - auto.
Qed.

Lemma type_wf_pi : forall Gamma A B,
  type_wf Gamma A -> type_wf (A::Gamma) B -> type_wf Gamma (TPi A B).
Proof. intros Gamma A B [j HA] [k HB]; exists (Nat.max j k); now apply ty_pi. Qed.

Lemma type_change_pi_codomain : forall Gamma A B D,
  type_wf Gamma A -> type_change (A::Gamma) B D ->
  type_change Gamma (TPi A B) (TPi A D).
Proof.
  intros Gamma A B D HA H; remember (A::Gamma) as Delta eqn:E.
  induction H; subst Delta.
  - apply tc_conversion; eauto using type_wf_pi.
    apply cv_compatible; constructor; auto using cv_refl.
  - apply tc_universe; eauto using type_wf_pi.
    constructor; auto using universe_le.
  - eapply tc_transitive; eauto.
Qed.

Lemma type_change_pi_domain : forall Gamma A C,
  type_change Gamma C A -> forall B, type_wf (A::Gamma) B ->
  type_change Gamma (TPi A B) (TPi C B).
Proof.
  intros Gamma A C H; induction H; intros D HD.
  - assert (HD' : type_wf (A::Gamma) D).
    { destruct HD as [k HD]; exists k.
      eapply type_change_narrowing; [eapply tc_conversion; eassumption|exact HD]. }
    apply tc_conversion; eauto using type_wf_pi.
    apply cv_compatible; constructor; auto using cv_refl, cv_sym.
  - assert (HD' : type_wf (A::Gamma) D).
    { destruct HD as [k HD]; exists k.
      eapply type_change_narrowing; [eapply tc_universe; eassumption|exact HD]. }
    apply tc_universe; eauto using type_wf_pi.
    constructor; auto using universe_le.
  - eapply tc_transitive; [apply IHtype_change2; exact HD|].
    apply IHtype_change1. destruct HD as [k HD]; exists k.
    eapply type_change_narrowing; eassumption.
Qed.

Theorem type_change_pi : forall Gamma A B C D,
  type_change Gamma C A -> type_wf (A::Gamma) B ->
  type_change (C::Gamma) B D -> type_change Gamma (TPi A B) (TPi C D).
Proof.
  intros Gamma A B C D HCA HB HBD; eapply tc_transitive.
  - apply type_change_pi_domain; eassumption.
  - apply type_change_pi_codomain; [exact (proj1 (type_change_formation _ _ _ HCA))|exact HBD].
Qed.

Lemma variable_change_generation : forall Gamma t T,
  typing Gamma t T -> forall n, t = TVar n ->
  exists A, nth_error Gamma n = Some A /\
    type_change Gamma (lift (S n) 0 A) T.
Proof.
  intros Gamma t T H; induction H; intros nn Heq; try discriminate.
  - inversion Heq; subst; exists A; split; [assumption|].
    apply type_change_refl; eexists; eassumption.
  - destruct (IHtyping1 _ Heq) as [C [HC HT]]; exists C; split; [exact HC|].
    eapply tc_transitive; [exact HT|apply tc_conversion; eauto using type_correctness; eexists; eassumption].
  - destruct (IHtyping _ Heq) as [C [HC HT]]; exists C; split; [exact HC|].
    eapply tc_transitive; [exact HT|apply tc_universe].
    + eapply type_correctness; eassumption.
    + eexists; apply ty_sort; eauto using typing_context.
    + now constructor.
  - destruct (IHtyping1 _ Heq) as [X [HX HT]]; exists X; split; [exact HX|].
    eapply tc_transitive; [exact HT|apply tc_universe; [eexists; exact H0|eexists; exact H1|now constructor]].
Qed.

Lemma application_change_generation : forall Gamma t T,
  typing Gamma t T -> forall f a, t = TApp f a ->
  exists A B, typing Gamma f (TPi A B) /\ typing Gamma a A /\
    type_change Gamma (subst a 0 B) T.
Proof.
  intros Gamma t T H; induction H; intros fn arg Heq; try discriminate.
  - inversion Heq; subst; exists A,B; repeat split; try assumption.
    apply type_change_refl; eexists; eassumption.
  - destruct (IHtyping1 _ _ Heq) as [X [Y [Hf [Ha HT]]]]; exists X,Y; repeat split; try assumption.
    eapply tc_transitive; [exact HT|apply tc_conversion; eauto using type_correctness; eexists; eassumption].
  - destruct (IHtyping _ _ Heq) as [X [Y [Hf [Ha HT]]]]; exists X,Y; repeat split; try assumption.
    eapply tc_transitive; [exact HT|apply tc_universe].
    + eapply type_correctness; eassumption.
    + eexists; apply ty_sort; eauto using typing_context.
    + now constructor.
  - destruct (IHtyping1 _ _ Heq) as [X [Y [Hf [Ha HT]]]]; exists X,Y; repeat split; try assumption.
    eapply tc_transitive; [exact HT|apply tc_universe; [eexists; exact H0|eexists; exact H1|now constructor]].
Qed.

Print Assumptions type_change_pi.
Print Assumptions variable_change_generation.
Print Assumptions application_change_generation.
