(* Candidate refinements for eliminators whose parameters and scrutinee reduce
   independently. The lemma is shared by indexed induction operators. *)
From Stdlib Require Import List.
Require Export nameless.DBSaturatedElimination.
Import Full.

Section EliminatorCandidate.
Context {Params : Type}.
Variable parameter_step : Params -> Params -> Prop.
Variable valid_parameter : Params -> Prop.
Variable construct : Params -> term -> term.
Variable domain : term -> Prop.
Variable result : Params -> term -> term -> Prop.
Hypothesis domain_candidate : candidate domain.
Hypothesis result_candidate : forall p, valid_parameter p -> forall t,
  domain t -> candidate (result p t).
Hypothesis result_stable : forall p, valid_parameter p -> stable_family domain (result p).
Hypothesis parameter_normalizing : forall p, valid_parameter p ->
  Acc (fun q p => parameter_step p q) p.
Hypothesis valid_reduct : forall p q,
  valid_parameter p -> parameter_step p q -> valid_parameter q.
Hypothesis parameter_stable : forall p q,
  valid_parameter p -> parameter_step p q -> forall t, domain t ->
  predicate_equiv (result p t) (result q t).
Hypothesis construct_argument : forall p, valid_parameter p -> forall t u,
  reduction t u -> reduction (construct p t) (construct p u).
Hypothesis construct_neutral : forall p, valid_parameter p -> forall t,
  neutral (construct p t).
Hypothesis construct_neutral_step : forall p, valid_parameter p -> forall t u,
  neutral t -> reduction (construct p t) u ->
  (exists q, parameter_step p q /\ u = construct q t) \/
  (exists t', reduction t t' /\ u = construct p t').

Definition eliminator_refinement t := domain t /\
  forall p, valid_parameter p -> result p t (construct p t).

Theorem eliminator_refinement_candidate : candidate eliminator_refinement.
Proof.
  constructor.
  - intros t [Ht _]; exact (candidate_normalizing domain_candidate Ht).
  - intros t u [Ht HC] HR; split; [exact (candidate_reduct domain_candidate Ht HR)|].
    intros p Hp; apply (proj1 (result_stable p Hp _ _ Ht HR _)).
    exact (candidate_reduct (result_candidate p Hp t Ht) (HC p Hp)
      (construct_argument p Hp t u HR)).
  - intros t HN HR.
    assert (Ht : domain t).
    { apply (candidate_neutral domain_candidate HN); intros u Hu; exact (proj1 (HR u Hu)). }
    split; [exact Ht|].
    intros p Hp; pose proof (parameter_normalizing p Hp) as HS; revert Hp.
    induction HS as [p HS IH]; intro Hp.
    apply (candidate_neutral (result_candidate p Hp t Ht) (construct_neutral p Hp t)).
    intros u Hu; destruct (construct_neutral_step p Hp t u HN Hu)
      as [[q [Hq ->]]|[t' [Ht' ->]]].
    + apply (proj2 (parameter_stable p q Hp Hq t Ht _)).
      exact (IH q Hq (valid_reduct p q Hp Hq)).
    + apply (proj2 (result_stable p Hp t t' Ht Ht' _)).
      exact (proj2 (HR t' Ht') p Hp).
Qed.
End EliminatorCandidate.

Print Assumptions eliminator_refinement_candidate.
