From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules.

(* A single beta redex, used twice in one pair. *)
Definition beta0 : term := TApp (TLam (TVar 0)) TUnitT.

Lemma beta0_step : step beta0 TUnitT.
Proof.
  unfold beta0.
  apply st_beta.
Qed.

(* The contextual pair rules can fire independently in both components. *)
Lemma pair_left_step :
    step (TPair beta0 beta0) (TPair TUnitT beta0).
Proof.
  apply st_pair1.
  exact beta0_step.
Qed.

Lemma pair_right_step :
    step (TPair beta0 beta0) (TPair beta0 TUnitT).
Proof.
  apply st_pair2.
  exact beta0_step.
Qed.

Lemma pair_results_distinct :
    TPair TUnitT beta0 <> TPair beta0 TUnitT.
Proof.
  intro H.
  inversion H.
Qed.

Lemma step_not_deterministic :
    exists t u v, step t u /\ step t v /\ u <> v.
Proof.
  exists (TPair beta0 beta0), (TPair TUnitT beta0), (TPair beta0 TUnitT).
  repeat split.
  - exact pair_left_step.
  - exact pair_right_step.
  - exact pair_results_distinct.
Qed.

Lemma eval_not_deterministic :
    exists t u v, eval t u /\ eval t v /\ u <> v.
Proof.
  exists (TPair beta0 beta0), (TPair TUnitT beta0), (TPair beta0 TUnitT).
  repeat split.
  - eapply ev_step.
    + exact pair_left_step.
    + apply ev_refl.
  - eapply ev_step.
    + exact pair_right_step.
    + apply ev_refl.
  - exact pair_results_distinct.
Qed.

(* The requested deterministic statements are therefore unprovable. *)
Theorem no_step_deterministic_statement :
    ~ (forall t u v, step t u -> step t v -> u = v).
Proof.
  intro H.
  destruct step_not_deterministic as [t [u [v [Hu [Hv Hneq]]]]].
  exact (Hneq (H t u v Hu Hv)).
Qed.

Theorem no_eval_deterministic_statement :
    ~ (forall t u v, eval t u -> eval t v -> u = v).
Proof.
  intro H.
  destruct eval_not_deterministic as [t [u [v [Hu [Hv Hneq]]]]].
  exact (Hneq (H t u v Hu Hv)).
Qed.
