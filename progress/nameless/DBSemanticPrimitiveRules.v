(* Semantic rules for the nonrecursive primitives and descriptions. *)
From Stdlib Require Import Arith Lia.
Require Export nameless.DBSemanticOperators.
Import Full.

Lemma semantic_unit_type : forall k, semantic_value TUnitT (TSort k).
Proof. intros; apply semantic_value_sort; exists full_SN; apply calculus_unit_type. Qed.
Lemma semantic_unit_value : semantic_value TUnit TUnitT.
Proof. eapply semantic_value_from_member; [exact (calculus_unit_type 0)|apply normal_form_accessible; intros u H; inversion H; discriminate]. Qed.
Lemma semantic_uid_type : semantic_value TUId (TSort 0).
Proof. apply semantic_value_sort; exists full_SN; apply calculus_uid_type. Qed.
Lemma semantic_tag : forall s, semantic_value (TTag s) TUId.
Proof. intros; eapply semantic_value_from_member; [exact (calculus_uid_type 0)|apply normal_form_accessible; intros u H; inversion H; discriminate]. Qed.
Lemma semantic_enumu_type : semantic_value TEnumU (TSort 0).
Proof. apply semantic_value_sort; exists enumeration_computable; apply calculus_enum_universe. Qed.
Lemma semantic_nile : semantic_value TNilE TEnumU.
Proof. eapply semantic_value_from_member; [exact (calculus_enum_universe 0)|constructor]. Qed.
Lemma semantic_conse : forall tag E, semantic_value tag TUId -> semantic_value E TEnumU ->
  semantic_value (TConsE tag E) TEnumU.
Proof.
  intros tag E Htag HE; eapply semantic_value_from_member; [exact (calculus_enum_universe 0)|].
  constructor; [exact (proj1 (semantic_value_normalizing _ _ Htag))|now apply semantic_enum_member].
Qed.
Lemma semantic_enumt : forall E, semantic_value E TEnumU -> semantic_value (TEnumT E) (TSort 0).
Proof.
  intros E HE; apply semantic_value_sort; exists (enum_elements E); apply calculus_enum_type.
  exact (proj1 (semantic_value_normalizing _ _ HE)).
Qed.
Lemma semantic_zero : forall tag E, semantic_value tag TUId -> semantic_value E TEnumU ->
  semantic_value TEZero (TEnumT (TConsE tag E)).
Proof.
  intros tag E HT HE.
  pose proof (proj1 (semantic_value_normalizing _ _ HT)) as HS.
  pose proof (proj1 (semantic_value_normalizing _ _ HE)) as HSE.
  eapply semantic_value_from_member with (n:=0); [apply calculus_enum_type; now apply full_SN_cons_enum|].
  now apply enum_zero_computable.
Qed.
Lemma semantic_succ : forall tag E e,
  semantic_value tag TUId -> semantic_value E TEnumU -> semantic_value e (TEnumT E) ->
  semantic_value (TESucc e) (TEnumT (TConsE tag E)).
Proof.
  intros tag E e HT HE He.
  pose proof (proj1 (semantic_value_normalizing _ _ HT)) as HS.
  pose proof (proj1 (semantic_value_normalizing _ _ HE)) as HSE.
  eapply semantic_value_from_member with (n:=0); [apply calculus_enum_type; now apply full_SN_cons_enum|].
  apply enum_succ_computable; [exact HS|exact HSE|].
  exact (semantic_value_member _ _ _ _ He (calculus_enum_type E HSE 0)).
Qed.
Lemma enum_family_type_interp : forall k E, full_SN E ->
  calculus_interp (S k) (TPi (TEnumT E) (TSort k))
    (dependent_function (enum_elements E) (fun _ => calculus_type k)).
Proof.
  intros k E HE; apply calculus_pi_interp; [now apply calculus_enum_type|].
  intros e He; apply calculus_sort_interp; lia.
Qed.
Lemma semantic_epi : forall k E P,
  semantic_value E TEnumU -> semantic_value P (TPi (TEnumT E) (TSort k)) ->
  semantic_value (TEPi k E P) (TSort k).
Proof.
  intros k E P HE HP.
  pose proof (semantic_enum_member _ HE) as HC.
  pose proof (semantic_value_member _ _ _ _ HP (enum_family_type_interp k E (enumeration_computable_normalizing _ HC))) as HF.
  apply semantic_value_sort, epi_computable; [exact HC|exact (proj1 HF)|exact (proj2 HF)].
Qed.
Lemma semantic_switch : forall k E P p e,
  semantic_value E TEnumU -> semantic_value P (TPi (TEnumT E) (TSort k)) ->
  semantic_value p (TEPi k E P) -> semantic_value e (TEnumT E) ->
  semantic_value (TSwitch k E P p e) (TApp P e).
Proof.
  intros k E P p e HE HP Hp He.
  pose proof (semantic_enum_member _ HE) as HC.
  pose proof (enumeration_computable_normalizing _ HC) as HS.
  pose proof (semantic_value_member _ _ _ _ HP (enum_family_type_interp k E HS)) as HF.
  exists k; apply switch_computable; [exact HC|exact (proj1 HF)|exact (proj2 HF)| |].
  - apply semantic_value_relevel; [exact Hp|apply epi_computable; [exact HC|exact (proj1 HF)|exact (proj2 HF)]].
  - exact (semantic_value_member _ _ _ _ He (calculus_enum_type E HS 0)).
Qed.
Lemma semantic_idesc : forall IT RI, small_interp IT RI -> semantic_value (TIDesc IT) (TSort 1).
Proof. intros; apply semantic_value_sort; exists (small_code RI); now apply calculus_description_formation. Qed.
Lemma semantic_description_value : forall IT RI D,
  small_interp IT RI -> small_code RI D -> semantic_value D (TIDesc IT).
Proof.
  intros IT RI D HI HD; eapply semantic_value_from_member;
    [exact (calculus_description_formation IT RI HI 1 ltac:(lia))|exact HD].
Qed.
Lemma semantic_ivar : forall IT RI i, small_interp IT RI -> semantic_value i IT ->
  semantic_value (TIVar i) (TIDesc IT).
Proof.
  intros IT RI i HI Hi; apply (semantic_description_value IT RI); [exact HI|].
  constructor; [exact (small_semantic_member _ _ _ Hi HI)|exact (proj1 (semantic_value_normalizing _ _ Hi))].
Qed.
Lemma semantic_i1 : forall IT RI, small_interp IT RI -> semantic_value TI1 (TIDesc IT).
Proof. intros; eapply semantic_description_value; [eassumption|constructor]. Qed.
Lemma semantic_ibot : forall IT RI, small_interp IT RI -> semantic_value TIBot (TIDesc IT).
Proof. intros; eapply semantic_description_value; [eassumption|constructor]. Qed.
Lemma semantic_iprod : forall IT RI A B,
  small_interp IT RI -> semantic_value A (TIDesc IT) -> semantic_value B (TIDesc IT) ->
  semantic_value (TIProd A B) (TIDesc IT).
Proof.
  intros IT RI A B HI HA HB; apply (semantic_description_value IT RI); [exact HI|].
  constructor; eapply semantic_description_member; eassumption.
Qed.
Lemma semantic_ipi : forall IT RI A D,
  small_interp IT RI -> semantic_value A (TSort 0) -> semantic_value D (arrow A (TIDesc IT)) ->
  semantic_value (TIPi A D) (TIDesc IT).
Proof.
  intros IT RI A D HI HA HD; destruct (small_semantic_type A HA) as [RA HRA].
  pose proof (semantic_description_function IT RI A RA D HI HRA HD) as HF.
  apply (semantic_description_value IT RI); [exact HI|].
  eapply dc_pi; [exact HRA|exact (proj1 HF)|exact (proj2 HF)].
Qed.
Lemma semantic_isig : forall IT RI A D,
  small_interp IT RI -> semantic_value A (TSort 0) -> semantic_value D (arrow A (TIDesc IT)) ->
  semantic_value (TISig A D) (TIDesc IT).
Proof.
  intros IT RI A D HI HA HD; destruct (small_semantic_type A HA) as [RA HRA].
  pose proof (semantic_description_function IT RI A RA D HI HRA HD) as HF.
  apply (semantic_description_value IT RI); [exact HI|].
  eapply dc_sigma; [exact HRA|exact (proj1 HF)|exact (proj2 HF)].
Qed.
Lemma semantic_ichoice : forall IT RI E D,
  small_interp IT RI -> semantic_value E TEnumU -> semantic_value D (arrow (TEnumT E) (TIDesc IT)) ->
  semantic_value (TIChoice E D) (TIDesc IT).
Proof.
  intros IT RI E D HI HE HD.
  pose proof (proj1 (semantic_value_normalizing _ _ HE)) as HSE.
  pose proof (universe_zero_small_type _ _ (calculus_enum_type E HSE 0)) as HET.
  pose proof (semantic_description_function IT RI (TEnumT E) _ D HI HET HD) as HF.
  apply (semantic_description_value IT RI); [exact HI|].
  eapply dc_choice; [exact HET|exact (proj1 HF)|exact (proj2 HF)].
Qed.

Print Assumptions semantic_epi.
Print Assumptions semantic_switch.
Print Assumptions semantic_ipi.
Print Assumptions semantic_ichoice.
