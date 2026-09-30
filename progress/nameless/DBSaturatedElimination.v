(* Dependent elimination from a saturated set of constructors. Parameters
   decrease independently, so the proof is shared by concrete eliminators. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBHeadExpansion nameless.DBIndexedCandidates.
Import Full.

Lemma stable_family_reductions : forall A B, candidate A -> stable_family A B ->
  forall t u, rtc reduction t u -> A t -> predicate_equiv (B t) (B u).
Proof.
  intros A B CA CB t u HR; induction HR; intro HT.
  - intro z; tauto.
  - pose proof (candidate_reduct CA HT H) as HY.
    intro v; pose proof (CB _ _ HT H v); pose proof (IHHR HY v); tauto.
Qed.

Section SaturatedElimination.
Context {Params : Type}.
Variable parameter_step : Params -> Params -> Prop.
Variable valid_parameter : Params -> Prop.
Variable construct : Params -> term -> term.
Variable seed : term -> Prop.
Hypothesis seed_normalizing : forall t, seed t -> full_SN t.
Variable result : term -> term -> Prop.
Hypothesis result_candidate : forall t, saturated seed t -> candidate (result t).
Hypothesis result_stable : stable_family (saturated seed) result.
Hypothesis valid_reduct : forall p q,
  valid_parameter p -> parameter_step p q -> valid_parameter q.
Hypothesis construct_argument : forall p, valid_parameter p -> forall t u,
  reduction t u -> reduction (construct p t) (construct p u).
Hypothesis construct_neutral : forall p, valid_parameter p -> forall t,
  neutral (construct p t).
Hypothesis construct_neutral_step : forall p, valid_parameter p -> forall t u,
  neutral t -> reduction (construct p t) u ->
  (exists q, parameter_step p q /\ u = construct q t) \/
  (exists t', reduction t t' /\ u = construct p t').
Hypothesis construct_seed : forall p, valid_parameter p -> forall t,
  seed t -> result t (construct p t).

Theorem saturated_elimination : forall p,
  Acc (fun q p => parameter_step p q) p -> valid_parameter p ->
  forall t, saturated seed t -> result t (construct p t).
Proof.
  intros p HP; induction HP as [p HP IH]; intro HV.
  pose proof (saturated_candidate seed seed_normalizing) as CD.
  assert (CR : candidate (fun t => saturated seed t /\ result t (construct p t))).
  { constructor.
    - intros t [HT _]; exact (candidate_normalizing CD HT).
    - intros t u [HT HC] HR; split; [exact (candidate_reduct CD HT HR)|].
      apply (proj1 (result_stable t u HT HR (construct p u))).
      exact (candidate_reduct (result_candidate t HT) HC (construct_argument p HV t u HR)).
    - intros t HN HR.
      assert (HT : saturated seed t).
      { apply (candidate_neutral CD HN); intros u HU; exact (proj1 (HR u HU)). }
      split; [exact HT|].
      apply (candidate_neutral (result_candidate t HT) (construct_neutral p HV t)).
      intros u HU; destruct (construct_neutral_step p HV t u HN HU)
        as [[q [Hq ->]]|[t' [Ht' ->]]].
      + apply (IH q Hq); [exact (valid_reduct p q HV Hq)|exact HT].
      + apply (proj2 (result_stable t t' HT Ht' (construct p t'))).
        exact (proj2 (HR t' Ht')). }
  intros t HT; refine (proj2 (HT _ CR _)).
  intros u HU; split; [now apply saturated_intro|exact (construct_seed p HV u HU)].
Qed.
End SaturatedElimination.

Print Assumptions saturated_elimination.
