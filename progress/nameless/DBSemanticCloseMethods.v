(* Interpreting the dependent motive and method accepted by close induction. *)
From Stdlib Require Import Arith Lia.
Require Export nameless.DBSemanticData.
Import Full.

Lemma close_motive_type_interp : forall IT RI G,
  small_interp IT RI -> computable_definition RI G ->
  calculus_interp 1 (close_motive IT G)
    (dependent_function (computable_definition RI) (fun D => dependent_function RI (fun i =>
      dependent_function (close_elements RI (definition_meaning RI G) D i) (fun _ => calculus_type 0)))).
Proof.
  intros IT RI G HI HG; apply calculus_pi_interp; [exact (definition_type_interp IT RI HI)|].
  intros D HD; cbn [subst]; rewrite ?subst_lift_prefix, ?lift_zero_id by lia.
  apply calculus_pi_interp; [now apply small_type_in_universe|].
  intros i Hi; cbn [subst CloseAt]; rewrite ?subst_lift_prefix, ?lift_zero_id by lia.
  cbn; rewrite ?subst_lift_zero, ?lift_zero_id.
  apply calculus_pi_interp.
  - apply small_type_in_universe; exact (semantic_close_family IT RI D G HI HD HG i Hi).
  - intros x Hx; apply calculus_sort_interp; lia.
Qed.
Lemma semantic_close_motive : forall IT RI G P,
  small_interp IT RI -> computable_definition RI G -> semantic_value P (close_motive IT G) ->
  full_SN P /\ close_motive_computable RI (definition_meaning RI G) P.
Proof.
  intros IT RI G P HI HG HP.
  pose proof (semantic_value_member _ _ _ _ HP (close_motive_type_interp IT RI G HI HG)) as HF.
  split; [exact (proj1 HF)|].
  intros D HD i x Hi Hx; apply calculus_zero_reducible; exact (proj2 (proj2 (proj2 HF D HD) i Hi) x Hx).
Qed.
Definition close_all_candidate IT G P D i xs :=
  type_elements small_atom (TIAll IT (TApp D i) (carrier IT G) xs (diagonal_motive G P)).
Lemma semantic_close_all_interp : forall IT RI G P D i xs,
  small_interp IT RI -> computable_definition RI G ->
  close_motive_computable RI (definition_meaning RI G) P ->
  computable_definition RI D -> RI i -> definition_meaning RI D i (definition_fixed_point RI G) xs ->
  small_interp (TIAll IT (TApp D i) (carrier IT G) xs (diagonal_motive G P))
    (close_all_candidate IT G P D i xs).
Proof.
  intros IT RI G P D i xs HI HG HP HD Hi Hxs; apply small_type_canonical.
  exact (close_all_type RI (small_type_candidate _ _ HI) G (definition_meaning RI G)
    (computable_definition_meaning RI (small_type_candidate _ _ HI) G HG)
    IT G P D i xs (type_interp_normalizing _ _ _ HI) (proj1 HG)
    (definition_is_interpreted RI (small_type_candidate _ _ HI) G HG) HP HD Hi Hxs).
Qed.
Ltac semantic_binder_subst :=
  repeat progress (cbn [subst payload carrier CloseAt Nat.ltb Nat.leb Nat.eqb Nat.pred];
    rewrite ?subst_lift_prefix, ?subst_diagonal_motive, ?lift_zero_id by lia).

Lemma close_ind_method_type_interp : forall IT RI G P,
  small_interp IT RI -> computable_definition RI G ->
  close_motive_computable RI (definition_meaning RI G) P ->
  calculus_interp 1 (close_ind_method IT G P)
    (dependent_function (computable_definition RI) (fun D => dependent_function RI (fun i =>
      dependent_function (definition_meaning RI D i (definition_fixed_point RI G)) (fun xs =>
        dependent_function (close_all_candidate IT G P D i xs)
          (fun _ => type_elements small_atom (TApp (TApp (TApp P D) i) (TIn xs))))))).
Proof.
  intros IT RI G P HI HG HP; apply calculus_pi_interp; [exact (definition_type_interp IT RI HI)|].
  intros D HD; semantic_binder_subst.
  apply calculus_pi_interp; [now apply small_type_in_universe|].
  intros i Hi; semantic_binder_subst.
  apply calculus_pi_interp.
  - apply small_type_in_universe.
    eapply semantic_interpretation_as; [exact HI|exact (proj2 HD i Hi)
      |exact (computable_definition_meaning RI (small_type_candidate _ _ HI) D HD i Hi)
      |unfold carrier; apply full_SN_close; [exact (type_interp_normalizing _ _ _ HI)|exact (proj1 HG)|exact (proj1 HG)]
      |exact (semantic_carrier_family IT RI G HI HG)].
  - intros xs Hxs; semantic_binder_subst.
    apply calculus_pi_interp.
    + apply small_type_in_universe; exact (semantic_close_all_interp IT RI G P D i xs HI HG HP HD Hi Hxs).
    + intros h Hh; semantic_binder_subst.
      apply small_type_in_universe, small_type_canonical, HP;
        [exact HD|exact Hi|now apply rolled_elements_intro].
Qed.
Lemma semantic_close_ind_method : forall IT RI G P st,
  small_interp IT RI -> computable_definition RI G ->
  close_motive_computable RI (definition_meaning RI G) P ->
  semantic_value st (close_ind_method IT G P) ->
  close_step_computable RI (definition_meaning RI G) IT G P st.
Proof.
  intros IT RI G P st HI HG HP Hst.
  pose proof (semantic_value_member _ _ _ _ Hst (close_ind_method_type_interp IT RI G P HI HG HP)) as HF.
  intros D HD i xs h Hi Hxs Hh.
  exists (type_elements small_atom (TApp (TApp (TApp P D) i) (TIn xs))); split.
  - apply small_type_canonical, HP; [exact HD|exact Hi|now apply rolled_elements_intro].
  - apply (proj2 (proj2 (proj2 (proj2 HF D HD) i Hi) xs Hxs)).
    exact (small_value_member _ _ _ Hh (semantic_close_all_interp IT RI G P D i xs HI HG HP HD Hi Hxs)).
Qed.

Print Assumptions semantic_close_motive.
Print Assumptions semantic_close_ind_method.
