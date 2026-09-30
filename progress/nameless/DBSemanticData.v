(* Semantic formation and constructor rules for reference and close data. *)
From Stdlib Require Import Arith Lia.
Require Export nameless.DBSemanticFamilies.
Import Full.

Definition definition_fixed_point RI D := description_fixed_point RI (definition_meaning RI D).
Lemma definition_is_interpreted : forall RI, candidate RI -> forall D,
  computable_definition RI D -> ind_definition RI (definition_meaning RI D) D.
Proof.
  intros RI CRI D HD i Hi; split; [exact (proj2 HD i Hi)|].
  exact (computable_definition_meaning RI CRI D HD i Hi).
Qed.
Lemma semantic_mu_family : forall IT RI D,
  small_interp IT RI -> computable_definition RI D ->
  interpreted_family RI (TMuI IT D) (definition_fixed_point RI D).
Proof.
  intros IT RI D HI HD i Hi; apply universe_zero_small_type, calculus_mu_type;
    [exact HI|exact (proj1 HD)|exact Hi|].
  exact (computable_definition_meaning RI (small_type_candidate _ _ HI) D HD).
Qed.
Lemma semantic_close_family : forall IT RI D G,
  small_interp IT RI -> computable_definition RI D -> computable_definition RI G ->
  interpreted_family RI (TClose IT D G)
    (fun i => rolled_elements (definition_meaning RI D i (definition_fixed_point RI G))).
Proof.
  intros IT RI D G HI HD HG i Hi; apply universe_zero_small_type, calculus_close_type;
    [exact HI|exact (proj1 HD)|exact (proj1 HG)|exact Hi| |];
    apply computable_definition_meaning; try assumption; exact (small_type_candidate _ _ HI).
Qed.
Lemma semantic_carrier_family : forall IT RI G,
  small_interp IT RI -> computable_definition RI G ->
  interpreted_family RI (carrier IT G) (definition_fixed_point RI G).
Proof.
  intros IT RI G HI HG i Hi; eapply it_equiv; [exact (semantic_close_family IT RI G G HI HG HG i Hi)|].
  intro t; symmetry; apply (small_fixed_point_rolled_equiv RI G (definition_meaning RI G));
    [exact (computable_definition_meaning RI (small_type_candidate _ _ HI) G HG)|exact Hi].
Qed.
Lemma semantic_mu : forall IT RI D,
  small_interp IT RI -> semantic_value D (Def IT) -> semantic_value (TMuI IT D) (Family IT).
Proof.
  intros IT RI D HI HD; pose proof (semantic_definition IT RI D HI HD) as HC.
  eapply semantic_value_from_member; [exact (family_type_interp IT RI HI)|].
  split; [apply full_SN_mui; [exact (type_interp_normalizing _ _ _ HI)|exact (proj1 HC)]|].
  intros i Hi; eexists; apply small_type_in_universe; exact (semantic_mu_family IT RI D HI HC i Hi).
Qed.
Lemma semantic_close : forall IT RI D G,
  small_interp IT RI -> semantic_value D (Def IT) -> semantic_value G (Def IT) ->
  semantic_value (TClose IT D G) (Family IT).
Proof.
  intros IT RI D G HI HD HG.
  pose proof (semantic_definition IT RI D HI HD) as HDC.
  pose proof (semantic_definition IT RI G HI HG) as HGC.
  eapply semantic_value_from_member; [exact (family_type_interp IT RI HI)|].
  split; [apply full_SN_close; [exact (type_interp_normalizing _ _ _ HI)|exact (proj1 HDC)|exact (proj1 HGC)]|].
  intros i Hi; eexists; apply small_type_in_universe; exact (semantic_close_family IT RI D G HI HDC HGC i Hi).
Qed.
Lemma semantic_interpretation_as : forall IT RI D X RX F,
  small_interp IT RI -> small_code RI D -> small_description RI D F ->
  full_SN X -> interpreted_family RI X RX -> small_interp (TInterp IT D X) (F RX).
Proof.
  intros IT RI D X RX F HI HD HM HX HF; eapply interpretation_computable_as;
    [exact (small_type_candidate _ _ HI)|exact HD|exact HM|exact (type_interp_normalizing _ _ _ HI)|exact HX|exact HF].
Qed.
Lemma semantic_in_mu : forall IT RI D i xs,
  small_interp IT RI -> semantic_value D (Def IT) -> semantic_value i IT ->
  semantic_value xs (TInterp IT (TApp D i) (TMuI IT D)) ->
  semantic_value (TIn xs) (MuAt IT D i).
Proof.
  intros IT RI D i xs HI HD Hi Hxs.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (semantic_definition IT RI D HI HD) as HDC.
  pose proof (small_semantic_member _ _ _ Hi HI) as Hic.
  pose proof (computable_definition_meaning RI CRI D HDC) as HM.
  pose proof (semantic_mu_family IT RI D HI HDC) as HF.
  eapply semantic_value_from_member with (n:=0); [apply small_type_in_universe; exact (HF i Hic)|].
  apply (ind_mu_fold RI D (definition_meaning RI D) HM); [exact Hic|].
  eapply small_semantic_member; [exact Hxs|].
  eapply semantic_interpretation_as; [exact HI|exact (proj2 HDC i Hic)|exact (HM i Hic)
    |apply full_SN_mui; [exact (type_interp_normalizing _ _ _ HI)|exact (proj1 HDC)]|exact HF].
Qed.
Lemma semantic_in_close : forall IT RI D G i xs,
  small_interp IT RI -> semantic_value D (Def IT) -> semantic_value G (Def IT) -> semantic_value i IT ->
  semantic_value xs (payload IT D G i) -> semantic_value (TIn xs) (CloseAt IT D G i).
Proof.
  intros IT RI D G i xs HI HD HG Hi Hxs.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (semantic_definition IT RI D HI HD) as HDC.
  pose proof (semantic_definition IT RI G HI HG) as HGC.
  pose proof (small_semantic_member _ _ _ Hi HI) as Hic.
  eapply semantic_value_from_member with (n:=0);
    [apply small_type_in_universe; exact (semantic_close_family IT RI D G HI HDC HGC i Hic)|].
  apply rolled_elements_intro; eapply small_semantic_member; [exact Hxs|].
  eapply semantic_interpretation_as; [exact HI|exact (proj2 HDC i Hic)
    |exact (computable_definition_meaning RI CRI D HDC i Hic)
    |unfold carrier; apply full_SN_close; [exact (type_interp_normalizing _ _ _ HI)|exact (proj1 HGC)|exact (proj1 HGC)]
    |exact (semantic_carrier_family IT RI G HI HGC)].
Qed.

Definition mu_all_candidate IT (RI : term -> Prop) D P i xs :=
  type_elements small_atom (TIAll IT (TApp D i) (TMuI IT D) xs P).
Lemma mu_all_interp : forall IT RI D P,
  small_interp IT RI -> computable_definition RI D -> full_SN P ->
  hypothesis_family RI (definition_fixed_point RI D) P -> forall i xs,
  RI i -> definition_meaning RI D i (definition_fixed_point RI D) xs ->
  small_interp (TIAll IT (TApp D i) (TMuI IT D) xs P) (mu_all_candidate IT RI D P i xs).
Proof.
  intros IT RI D P HI HD HP HM i xs Hi Hxs; apply small_type_canonical.
  eapply all_computable; [exact (small_type_candidate _ _ HI)|exact (proj2 HD i Hi)
    |exact (computable_definition_meaning RI (small_type_candidate _ _ HI) D HD i Hi)
    |exact (type_interp_normalizing _ _ _ HI)
    |apply full_SN_mui; [exact (type_interp_normalizing _ _ _ HI)|exact (proj1 HD)]|exact HP
    |exact (interpreted_family_stable _ _ _ (semantic_mu_family IT RI D HI HD))|exact HM|exact Hxs].
Qed.
Lemma mu_ind_method_type_interp : forall IT RI D P,
  small_interp IT RI -> computable_definition RI D -> full_SN P ->
  hypothesis_family RI (definition_fixed_point RI D) P ->
  small_interp (mu_ind_method IT D P)
    (dependent_function RI (fun i =>
      dependent_function (definition_meaning RI D i (definition_fixed_point RI D)) (fun xs =>
        dependent_function (mu_all_candidate IT RI D P i xs)
          (fun _ => type_elements small_atom (TApp P (TPair i (TIn xs))))))).
Proof.
  intros IT RI D P HI HD HP HM.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (computable_definition_meaning RI CRI D HD) as HDM.
  apply small_pi_interp; [exact HI|].
  intros i Hi; cbn [subst]; rewrite ?subst_lift_prefix, ?lift_zero_id by lia.
  apply small_pi_interp.
  - eapply semantic_interpretation_as; [exact HI|exact (proj2 HD i Hi)|exact (HDM i Hi)
      |apply full_SN_mui; [exact (type_interp_normalizing _ _ _ HI)|exact (proj1 HD)]
      |exact (semantic_mu_family IT RI D HI HD)].
  - intros xs Hxs; cbn [subst]; rewrite ?subst_lift_prefix, ?lift_zero_id by lia.
    cbn; rewrite ?subst_lift_zero, ?lift_zero_id.
    apply small_pi_interp; [exact (mu_all_interp IT RI D P HI HD HP HM i xs Hi Hxs)|].
    intros h Hh; cbn [subst]; rewrite ?subst_lift_prefix, ?lift_zero_id by lia.
    apply small_type_canonical, HM; [exact Hi|].
    apply (ind_mu_fold RI D (definition_meaning RI D) HDM); assumption.
Qed.
Lemma semantic_mu_ind_method : forall IT RI D P st,
  small_interp IT RI -> computable_definition RI D -> full_SN P ->
  hypothesis_family RI (definition_fixed_point RI D) P ->
  semantic_value st (mu_ind_method IT D P) -> ind_method RI (definition_meaning RI D) IT D P st.
Proof.
  intros IT RI D P st HI HD HP HM Hst.
  pose proof (small_semantic_member _ _ _ Hst (mu_ind_method_type_interp IT RI D P HI HD HP HM)) as HF.
  intros i xs h Hi Hxs Hh.
  pose proof (mu_all_interp IT RI D P HI HD HP HM i xs Hi Hxs) as HA.
  exists (type_elements small_atom (TApp P (TPair i (TIn xs)))); split.
  - apply small_type_canonical, HM; [exact Hi|].
    apply (ind_mu_fold RI D (definition_meaning RI D)
      (computable_definition_meaning RI (small_type_candidate _ _ HI) D HD)); assumption.
  - apply (proj2 (proj2 (proj2 HF i Hi) xs Hxs)).
    exact (small_value_member _ _ _ Hh HA).
Qed.

Print Assumptions semantic_mu.
Print Assumptions semantic_close.
Print Assumptions semantic_in_mu.
Print Assumptions semantic_in_close.
Print Assumptions semantic_mu_ind_method.
