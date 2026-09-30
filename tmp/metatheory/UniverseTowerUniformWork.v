From Stdlib Require Import List Arith Bool Lia.
Require Export SemanticTypesWork.
Import ListNotations Full.

Section UniverseTower.
Variable base : term -> (term -> Prop) -> Prop.
Hypothesis base_candidate : forall n R, base n R -> candidate R.
Hypothesis base_not_neutral : forall n R, base n R -> ~ neutral n.
Hypothesis base_not_pi : forall A B R, ~ base (TPi A B) R.
Hypothesis base_not_sigma : forall A B R, ~ base (TSigma A B) R.
Hypothesis base_not_sort : forall k R, ~ base (TSort k) R.
Hypothesis base_unique : forall n R S,
  base n R -> base n S -> predicate_equiv R S.

Inductive level_atom (levels : list (term -> Prop)) : term -> (term -> Prop) -> Prop :=
| la_base : forall n R, base n R -> level_atom levels n R
| la_sort : forall k R, nth_error levels k = Some R -> level_atom levels (TSort k) R.
Lemma level_atom_not_neutral : forall levels n R, level_atom levels n R -> ~ neutral n.
Proof. intros levels n R H; destruct H; [eapply base_not_neutral; eassumption|cbn [neutral]; tauto]. Qed.
Lemma level_atom_not_pi : forall levels A B R, ~ level_atom levels (TPi A B) R.
Proof. intros levels A B R H; inversion H; subst; eapply base_not_pi; eassumption. Qed.
Lemma level_atom_not_sigma : forall levels A B R, ~ level_atom levels (TSigma A B) R.
Proof. intros levels A B R H; inversion H; subst; eapply base_not_sigma; eassumption. Qed.
Lemma level_atom_unique : forall levels n R S,
  level_atom levels n R -> level_atom levels n S -> predicate_equiv R S.
Proof.
  intros levels n R S H; destruct H; intro H'; inversion H'; subst.
  - eapply base_unique; eassumption.
  - exfalso; eapply base_not_sort; eassumption.
  - exfalso; eapply base_not_sort; eassumption.
  - match goal with H : nth_error _ _ = Some _, H' : nth_error _ _ = Some _ |- _ =>
      rewrite H in H'; inversion H'; subst end; intro t; tauto.
Qed.
Lemma level_atom_candidate : forall levels,
  Forall candidate levels -> forall n R, level_atom levels n R -> candidate R.
Proof.
  intros levels HC n R H; destruct H; [eapply base_candidate; eassumption|].
  eapply Forall_forall; [exact HC|now apply nth_error_In with k].
Qed.
Lemma layer_universe_candidate : forall levels, Forall candidate levels ->
  candidate (reducible_type (level_atom levels)).
Proof. intros; apply reducible_type_candidate.
Qed.

Fixpoint universe_levels n : list (term -> Prop) :=
  match n with
  | 0 => []
  | S k => let previous := universe_levels k in
      previous ++ [reducible_type (level_atom previous)]
  end.
Definition universe_model n := reducible_type (level_atom (universe_levels n)).
Definition universe_interp n := type_interp (level_atom (universe_levels n)).
Lemma universe_levels_candidates : forall n, Forall candidate (universe_levels n).
Proof.
  induction n; cbn [universe_levels]; [constructor|apply Forall_app; split; [exact IHn|]].
  constructor; [now apply layer_universe_candidate|constructor].
Qed.
Theorem universe_model_candidate : forall n, candidate (universe_model n).
Proof. intros n; apply layer_universe_candidate, universe_levels_candidates. Qed.
Lemma universe_levels_length : forall n, length (universe_levels n) = n.
Proof. induction n; cbn [universe_levels]; [reflexivity|rewrite length_app, IHn; cbn; lia]. Qed.
Lemma universe_levels_lookup : forall k n, k < n ->
  nth_error (universe_levels n) k = Some (universe_model k).
Proof.
  intros k n; revert k; induction n; intros k H; [lia|].
  cbn [universe_levels]; destruct (Nat.eq_dec k n) as [->|Hne].
  - rewrite nth_error_app2 by (rewrite universe_levels_length; lia).
    rewrite universe_levels_length, Nat.sub_diag; reflexivity.
  - rewrite nth_error_app1 by (rewrite universe_levels_length; lia).
    apply IHn; lia.
Qed.

Lemma type_interp_monotone : forall atoms atoms',
  (forall n R, atoms n R -> atoms' n R) ->
  forall A R, type_interp atoms A R -> type_interp atoms' A R.
Proof.
  intros atoms atoms' HA A R H; induction H;
    first [eapply it_neutral; eassumption|eapply it_atom; [eassumption|eassumption|eassumption|now apply HA]
      |eapply it_pi; eassumption|eapply it_sigma; eassumption|eapply it_equiv; eassumption].
Qed.
Lemma level_atom_cumulative : forall n m, n <= m -> forall A R,
  level_atom (universe_levels n) A R -> level_atom (universe_levels m) A R.
Proof.
  intros n m Hnm A R H; destruct H; [now apply la_base|].
  assert (Hkn : k < n).
  { rewrite <- universe_levels_length. apply nth_error_Some; congruence. }
  pose proof (universe_levels_lookup k n Hkn) as HE.
  rewrite H in HE; inversion HE; subst R.
  apply la_sort, universe_levels_lookup; lia.
Qed.
Theorem universe_interp_cumulative : forall n m, n <= m -> forall A R,
  universe_interp n A R -> universe_interp m A R.
Proof.
  intros n m Hnm; apply type_interp_monotone.
  now apply level_atom_cumulative.
Qed.
Theorem universe_model_cumulative : forall n m, n <= m -> forall A,
  universe_model n A -> universe_model m A.
Proof.
  intros n m Hnm A [R HR]; exists R; eapply universe_interp_cumulative; eassumption.
Qed.
Lemma sort_normal : forall k, normal_form (TSort k).
Proof. intros k u H; inversion H; discriminate. Qed.
Theorem universe_sort_interpretation : forall k n, k < n ->
  universe_interp n (TSort k) (universe_model k).
Proof.
  intros k n H; eapply it_atom with (n:=TSort k).
  - apply normal_form_accessible, sort_normal.
  - constructor.
  - apply sort_normal.
  - apply la_sort; now apply universe_levels_lookup.
Qed.
Theorem universe_sort_computable : forall k, universe_model (S k) (TSort k).
Proof. intros k; exists (universe_model k); apply universe_sort_interpretation; lia. Qed.

Theorem universe_interp_candidate : forall n A R,
  universe_interp n A R -> candidate R.
Proof.
  intros n A R H; eapply type_interp_candidate; [| | | | |exact H].
  - apply level_atom_candidate, universe_levels_candidates.
  - apply level_atom_not_neutral.
  - apply level_atom_not_pi.
  - apply level_atom_not_sigma.
  - apply level_atom_unique.
Qed.
Theorem universe_interp_unique : forall n m A B R S,
  universe_interp n A R -> universe_interp m B S -> conv A B -> predicate_equiv R S.
Proof.
  intros n m A B R S HA HB HC.
  pose proof (universe_interp_cumulative n (Nat.max n m) (Nat.le_max_l _ _) _ _ HA) as HA'.
  pose proof (universe_interp_cumulative m (Nat.max n m) (Nat.le_max_r _ _) _ _ HB) as HB'.
  eapply (type_interp_unique (level_atom (universe_levels (Nat.max n m))));
    [apply level_atom_not_neutral|apply level_atom_not_pi|apply level_atom_not_sigma
    |apply level_atom_unique|exact HA'|exact HB'|exact HC].
Qed.

Definition universe_elements n A := type_elements (level_atom (universe_levels n)) A.
Lemma universe_interp_canonical : forall n A,
  universe_model n A -> universe_interp n A (universe_elements n A).
Proof.
  intros n A H; apply type_interp_canonical;
    [apply level_atom_not_neutral|apply level_atom_not_pi|apply level_atom_not_sigma
    |apply level_atom_unique|exact H].
Qed.
Theorem universe_pi_formation : forall j k U V,
  universe_model j U ->
  (forall a, universe_elements j U a -> universe_model k (subst a 0 V)) ->
  universe_model (Nat.max j k) (TPi U V).
Proof.
  intros j k U V HU HV.
  exists (dependent_function (universe_elements j U)
    (fun a => universe_elements k (subst a 0 V))).
  eapply type_interp_pi_intro.
  - apply level_atom_candidate, universe_levels_candidates.
  - apply level_atom_not_neutral.
  - apply level_atom_not_pi.
  - apply level_atom_not_sigma.
  - apply level_atom_unique.
  - apply (universe_interp_cumulative j (Nat.max j k) (Nat.le_max_l _ _)).
    now apply universe_interp_canonical.
  - intros a HA. apply (universe_interp_cumulative k (Nat.max j k) (Nat.le_max_r _ _)).
    apply universe_interp_canonical, HV; exact HA.
Qed.
Theorem universe_sigma_formation : forall j k U V,
  universe_model j U ->
  (forall a, universe_elements j U a -> universe_model k (subst a 0 V)) ->
  universe_model (Nat.max j k) (TSigma U V).
Proof.
  intros j k U V HU HV.
  exists (dependent_pair (universe_elements j U)
    (fun a => universe_elements k (subst a 0 V))).
  eapply type_interp_sigma_intro.
  - apply level_atom_candidate, universe_levels_candidates.
  - apply level_atom_not_neutral.
  - apply level_atom_not_pi.
  - apply level_atom_not_sigma.
  - apply level_atom_unique.
  - apply (universe_interp_cumulative j (Nat.max j k) (Nat.le_max_l _ _)).
    now apply universe_interp_canonical.
  - intros a HA. apply (universe_interp_cumulative k (Nat.max j k) (Nat.le_max_r _ _)).
    apply universe_interp_canonical, HV; exact HA.
Qed.
End UniverseTower.

Print Assumptions universe_model_candidate.
Print Assumptions universe_model_cumulative.
Print Assumptions universe_sort_computable.
Print Assumptions universe_interp_unique.
Print Assumptions universe_pi_formation.
Print Assumptions universe_sigma_formation.
