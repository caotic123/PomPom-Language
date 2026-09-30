(* Semantic meanings of the derived family and motive types. These extract
   the pointwise hypotheses required by the primitive operator proofs. *)
From Stdlib Require Import Arith Lia.
Require Export nameless.DBSemanticSubstitution.
Import Full.

Lemma calculus_pi_interp : forall n A B RA RB,
  calculus_interp n A RA ->
  (forall a, RA a -> calculus_interp n (subst a 0 B) (RB a)) ->
  calculus_interp n (TPi A B) (dependent_function RA RB).
Proof.
  intros; eapply type_interp_pi_intro.
  - apply level_atom_candidate; [exact primitive_candidate|apply universe_levels_candidates].
  - apply level_atom_not_neutral; exact primitive_not_neutral.
  - apply level_atom_not_pi; exact primitive_not_pi.
  - apply level_atom_not_sigma; exact primitive_not_sigma.
  - apply level_atom_unique; [exact primitive_not_sort|exact primitive_unique].
  - eassumption.
  - eassumption.
Qed.
Lemma calculus_zero_reducible : forall A, calculus_type 0 A -> reducible_type small_atom A.
Proof. intros A [R HA]; exists R; now apply universe_zero_small_type. Qed.
Lemma small_semantic_value : forall t A, small_value t A -> semantic_value t A.
Proof. intros t A [R [HR Ht]]; exists 0,R; split; [now apply small_type_in_universe|exact Ht]. Qed.
Lemma small_semantic_member : forall t A R, semantic_value t A -> small_interp A R -> R t.
Proof. intros; eapply semantic_value_member; [eassumption|now apply small_type_in_universe with (n:=0)]. Qed.
Lemma small_semantic_type : forall A, semantic_value A (TSort 0) -> reducible_type small_atom A.
Proof. intros; apply calculus_zero_reducible; now apply semantic_value_sort. Qed.
Lemma semantic_small_sort : forall A, reducible_type small_atom A -> semantic_value A (TSort 0).
Proof. intros A [R HA]; apply semantic_value_sort; exists R; now apply small_type_in_universe. Qed.

Lemma family_type_interp : forall IT RI, small_interp IT RI ->
  calculus_interp 1 (Family IT) (dependent_function RI (fun _ => calculus_type 0)).
Proof.
  intros IT RI HI; apply calculus_pi_interp; [now apply small_type_in_universe|].
  intros i Hi; cbn [subst]; apply calculus_sort_interp; lia.
Qed.
Lemma definition_type_interp : forall IT RI, small_interp IT RI ->
  calculus_interp 1 (Def IT) (dependent_function RI (fun _ => small_code RI)).
Proof.
  intros IT RI HI; apply calculus_pi_interp; [now apply small_type_in_universe|].
  intros i Hi; cbn [subst]; rewrite subst_lift_zero; now apply calculus_description_formation.
Qed.
Lemma semantic_family : forall IT RI X,
  small_interp IT RI -> semantic_value X (Family IT) ->
  full_SN X /\ interpreted_family RI X (fun i => type_elements small_atom (TApp X i)).
Proof.
  intros IT RI X HI HX.
  pose proof (semantic_value_member _ _ _ _ HX (family_type_interp IT RI HI)) as HF.
  split; [exact (proj1 HF)|].
  intros i Hi; apply small_type_canonical, calculus_zero_reducible; exact (proj2 HF i Hi).
Qed.
Lemma semantic_definition : forall IT RI D,
  small_interp IT RI -> semantic_value D (Def IT) -> computable_definition RI D.
Proof. intros IT RI D HI HD; exact (semantic_value_member _ _ _ _ HD (definition_type_interp IT RI HI)). Qed.
Lemma total_type_interp : forall IT RI X RX,
  small_interp IT RI -> interpreted_family RI X RX ->
  small_interp (total IT X) (dependent_pair RI RX).
Proof.
  intros IT RI X RX HI HX; apply small_sigma_interp; [exact HI|].
  intros i Hi; cbn [subst]; rewrite subst_lift_zero, lift_zero_id; exact (HX i Hi).
Qed.
Lemma motive_type_interp : forall IT RI X RX,
  small_interp IT RI -> interpreted_family RI X RX ->
  calculus_interp 1 (motive IT X) (dependent_function (dependent_pair RI RX) (fun _ => calculus_type 0)).
Proof.
  intros IT RI X RX HI HX; apply calculus_pi_interp.
  - apply small_type_in_universe; now apply total_type_interp.
  - intros p Hp; apply calculus_sort_interp; lia.
Qed.
Lemma semantic_motive : forall IT RI X RX P,
  small_interp IT RI -> interpreted_family RI X RX -> semantic_value P (motive IT X) ->
  full_SN P /\ hypothesis_family RI RX P.
Proof.
  intros IT RI X RX P HI HX HP.
  pose proof (semantic_value_member _ _ _ _ HP (motive_type_interp IT RI X RX HI HX)) as HF.
  split; [exact (proj1 HF)|].
  intros i x Hi Hx; apply calculus_zero_reducible, (proj2 HF).
  apply dependent_pair_computable; [exact (small_type_candidate _ _ HI)
    |exact (proj1 (interpreted_family_stable _ _ _ HX))| |exact Hi|exact Hx].
  intros i0 i1 H0 HR; apply (proj2 (interpreted_family_stable _ _ _ HX) i0 i1);
    [exact H0|exact (candidate_reduct (small_type_candidate _ _ HI) H0 HR)|now apply reductions_conversion, rtc_one].
Qed.
Lemma recursive_method_type_interp : forall IT RI X RX P,
  small_interp IT RI -> interpreted_family RI X RX -> hypothesis_family RI RX P ->
  small_interp (recursive_method IT X P)
    (dependent_function RI (fun i => dependent_function (RX i)
      (fun x => type_elements small_atom (TApp P (TPair i x))))).
Proof.
  intros IT RI X RX P HI HX HP; apply small_pi_interp; [exact HI|].
  intros i Hi; cbn [subst]; rewrite ?subst_lift_prefix, ?lift_zero_id by lia.
  apply small_pi_interp; [exact (HX i Hi)|].
  intros x Hx; cbn [subst]; rewrite ?subst_lift_prefix, ?lift_zero_id by lia.
  cbn; rewrite ?subst_lift_zero, ?lift_zero_id.
  apply small_type_canonical; exact (HP i x Hi Hx).
Qed.
Lemma semantic_recursive_method : forall IT RI X RX P h,
  small_interp IT RI -> interpreted_family RI X RX -> hypothesis_family RI RX P ->
  semantic_value h (recursive_method IT X P) -> hypothesis_method RI RX P h.
Proof.
  intros IT RI X RX P h HI HX HP Hh.
  pose proof (small_semantic_member _ _ _ Hh (recursive_method_type_interp IT RI X RX P HI HX HP)) as HF.
  split; [exact (proj1 HF)|]; intros i x Hi Hx.
  exists (type_elements small_atom (TApp P (TPair i x))); split;
    [apply small_type_canonical; exact (HP i x Hi Hx)|exact (proj2 (proj2 HF i Hi) x Hx)].
Qed.

Print Assumptions semantic_family.
Print Assumptions semantic_definition.
Print Assumptions semantic_motive.
Print Assumptions semantic_recursive_method.
