(* Computability of the description interpretation operator. Argument
   reduction is handled by the shared head-expansion theorem. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBSemanticGeneration nameless.DBHeadExpansion.
Import ListNotations Full.

Definition small_interp := type_interp small_atom.
Definition small_description := description_interp small_atom.
Definition small_code := description_computable small_atom.
Definition code_meaning := description_elements small_atom.

Lemma small_interp_unique : forall A B R S,
  small_interp A R -> small_interp B S -> conv A B -> predicate_equiv R S.
Proof.
  intros; eapply type_interp_unique; [exact small_atom_not_neutral|exact small_atom_not_pi
    |exact small_atom_not_sigma|intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)
    |eassumption|eassumption|eassumption].
Qed.
Lemma small_description_unique : forall RI D F RI' E G,
  small_description RI D F -> small_description RI' E G -> conv D E -> functor_equiv F G.
Proof.
  intros; eapply description_interp_unique; [exact small_atom_not_neutral|exact small_atom_not_pi
    |exact small_atom_not_sigma|intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)
    |eassumption|eassumption|eassumption].
Qed.
Lemma small_code_meaning : forall RI, candidate RI -> forall D, small_code RI D ->
  small_description RI D (code_meaning RI D).
Proof.
  intros RI CRI D HD; apply description_interp_canonical;
    [exact small_atom_not_neutral|exact small_atom_not_pi|exact small_atom_not_sigma
    |intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)|].
  eapply computable_description_interpreted;
    [exact small_atom_not_neutral|exact small_atom_not_pi|exact small_atom_not_sigma
    |intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)|exact CRI|exact HD].
Qed.
Lemma small_pi_interp : forall A B RA RB,
  small_interp A RA -> (forall a, RA a -> small_interp (subst a 0 B) (RB a)) ->
  small_interp (TPi A B) (dependent_function RA RB).
Proof.
  intros; eapply type_interp_pi_intro;
    [exact small_atom_candidate|exact small_atom_not_neutral|exact small_atom_not_pi
    |exact small_atom_not_sigma|intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)
    |eassumption|eassumption].
Qed.
Lemma small_sigma_interp : forall A B RA RB,
  small_interp A RA -> (forall a, RA a -> small_interp (subst a 0 B) (RB a)) ->
  small_interp (TSigma A B) (dependent_pair RA RB).
Proof.
  intros; eapply type_interp_sigma_intro;
    [exact small_atom_candidate|exact small_atom_not_neutral|exact small_atom_not_pi
    |exact small_atom_not_sigma|intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)
    |eassumption|eassumption].
Qed.
Lemma small_product_interp : forall A B RA RB,
  small_interp A RA -> small_interp B RB ->
  small_interp (product A B) (dependent_pair RA (fun _ => RB)).
Proof.
  intros A B RA RB HA HB; apply small_sigma_interp; [exact HA|].
  intros a Ha; now rewrite subst_lift_zero.
Qed.
Lemma small_unit_interp : small_interp TUnitT full_SN.
Proof. apply universe_zero_small_type, calculus_unit_type. Qed.
Lemma small_bottom_interp : small_interp Bot empty_elements.
Proof.
  eapply it_equiv; [apply universe_zero_small_type, calculus_enum_type;
    apply normal_form_accessible, nil_enum_normal|exact enum_elements_empty].
Qed.

Definition interpreted_family (RI : term -> Prop) X (RX : payload_family) :=
  forall i, RI i -> small_interp (TApp X i) (RX i).
Definition stable_indexed_family RI (RX : payload_family) :=
  Indexed.candidates RI RX /\ forall i j, RI i -> RI j -> conv i j -> predicate_equiv (RX i) (RX j).
Lemma interpreted_family_stable : forall RI X RX,
  interpreted_family RI X RX -> stable_indexed_family RI RX.
Proof.
  intros RI X RX H; split.
  - intros i Hi; exact (small_type_candidate _ _ (H i Hi)).
  - intros i j Hi Hj HC; eapply small_interp_unique; [exact (H i Hi)|exact (H j Hj)|].
    apply cv_compatible, cp_TApp; [apply cv_refl|exact HC].
Qed.
Lemma interpreted_family_reductions : forall RI X RX,
  interpreted_family RI X RX -> forall X', rtc reduction X X' -> interpreted_family RI X' RX.
Proof.
  intros RI X RX HX X' HR i Hi; eapply type_interp_reductions;
    [exact (HX i Hi)|apply red_star_TApp; [exact HR|constructor]].
Qed.

Definition interpretation_roots RI D := forall D', rtc reduction D D' ->
  forall IT X RX, full_SN IT -> full_SN X -> interpreted_family RI X RX ->
  forall F, small_description RI D' F -> forall v,
  root_step (TInterp IT D' X) = Some v -> small_interp v (F RX).
Lemma interpretation_roots_reductions : forall RI D, interpretation_roots RI D ->
  forall E, rtc reduction D E -> interpretation_roots RI E.
Proof.
  intros RI D HD E HR F HE; apply HD; eapply rtc_trans; eassumption.
Qed.

Lemma neutral_interpretation_normal : forall IT D X,
  normal_form IT -> normal_form D -> normal_form X -> neutral D ->
  normal_form (TInterp IT D X).
Proof.
  intros IT D X HI HD HX HN u HU; inversion HU; subst.
  - destruct D; cbn [neutral root_step] in *; contradiction || discriminate.
  - eapply HI; eassumption.
  - eapply HD; eassumption.
  - eapply HX; eassumption.
Qed.

Lemma interpretation_meaning_at_root : forall RI D F IT X RX,
  small_description RI D F -> interpretation_roots RI D ->
  full_SN IT -> full_SN X -> interpreted_family RI X RX ->
  full_SN (TInterp IT D X) -> forall E v,
  rtc reduction D E -> root_step (TInterp IT E X) = Some v ->
  small_interp (TInterp IT D X) (F RX).
Proof.
  intros RI D F IT X RX HD HR HI HX HF HS E v HE HV.
  assert (HDE : small_description RI E F) by (eapply description_interp_reductions; eassumption).
  eapply type_interp_conversion; [exact (HR E HE IT X RX HI HX HF F HDE v HV)|exact HS|].
  apply cv_sym; apply reductions_conversion.
  eapply rtc_trans; [apply red_star_TInterp; [constructor|exact HE|constructor]|].
  apply rtc_one, red_root; exact HV.
Qed.

Lemma interpretation_meaning_from_roots : forall RI D F,
  small_description RI D F -> interpretation_roots RI D ->
  forall IT X RX, full_SN IT -> full_SN X -> interpreted_family RI X RX ->
  full_SN (TInterp IT D X) -> small_interp (TInterp IT D X) (F RX).
Proof.
  intros RI D F HD; pose proof HD as Hwhole; induction HD;
    intros HR IT X RX HI HX HF HS.
  all: try solve [eapply (interpretation_meaning_at_root _ _ _ _ _ _ Hwhole HR HI HX HF HS);
    [exact H0|reflexivity]].
  - destruct (normalize_full _ HI) as [IT' [RIT NIT]].
    destruct (normalize_full _ HX) as [X' [RX' NX]].
    eapply it_neutral with (n:=TInterp IT' n X').
    + exact HS.
    + now apply red_star_TInterp.
    + now apply neutral_interpretation_normal.
    + exact I.
  - eapply it_equiv; [eapply IHHD; eassumption|exact (H RX)].
Qed.

Theorem interpretation_from_roots : forall RI D F,
  small_description RI D F -> interpretation_roots RI D ->
  forall IT X RX, full_SN IT -> full_SN X -> interpreted_family RI X RX ->
  small_interp (TInterp IT D X) (F RX).
Proof.
  intros RI D F HD HR IT X RX HI HX HF.
  assert (HT : reducible_type small_atom (TInterp IT D X)).
  { apply computability_by_head_expansion; [apply reducible_type_candidate| | |].
    - cbn [term_children]; constructor; [exact HI|].
      constructor; [exact (description_interp_normalizing _ _ _ _ HD)|].
      constructor; [exact HX|constructor].
    - intros u HU; inversion HU; exact I.
    - intros u v HU HV; inversion HU; subst; inversion HV; subst.
      eexists; eapply HR; [eassumption| | | | |eassumption].
      + exact (full_SN_reductions _ HI _ H2).
      + exact (full_SN_reductions _ HX _ H5).
      + eapply interpreted_family_reductions; eassumption.
      + eapply description_interp_reductions; eassumption. }
  apply (interpretation_meaning_from_roots _ _ _ HD HR IT X RX HI HX HF).
  destruct HT as [R HRT]; exact (type_interp_normalizing _ _ _ HRT).
Qed.
Lemma interpretation_from_code_roots : forall RI, candidate RI -> forall D,
  small_code RI D -> interpretation_roots RI D ->
  forall IT X RX, full_SN IT -> full_SN X -> interpreted_family RI X RX ->
  small_interp (TInterp IT D X) (code_meaning RI D RX).
Proof. intros; eapply interpretation_from_roots; [eapply small_code_meaning; eassumption|eassumption|eassumption|eassumption|eassumption]. Qed.

Lemma reduces_unary : forall C : term -> term,
  (forall a u, reduction (C a) u -> exists a', u = C a' /\ rtc reduction a a') ->
  forall a u, rtc reduction (C a) u -> exists a', u = C a' /\ rtc reduction a a'.
Proof.
  intros C HC a u H; remember (C a) as t eqn:HE; revert a HE.
  induction H; intros a HE; subst.
  - exists a; split; [reflexivity|constructor].
  - destruct (HC _ _ H) as [a' [-> HR]].
    destruct (IHrtc _ eq_refl) as [a'' [-> HR']].
    exists a''; split; [reflexivity|eapply rtc_trans; eassumption].
Qed.
Lemma ivar_reductions : forall i D, rtc reduction (TIVar i) D ->
  exists j, D = TIVar j /\ rtc reduction i j.
Proof.
  apply reduces_unary; intros i D H; inversion H; subst; [discriminate|].
  eexists; split; [reflexivity|now apply rtc_one].
Qed.
Lemma iprod_reduction : forall A B D, reduction (TIProd A B) D ->
  exists A' B', D = TIProd A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Proof. intros; match goal with H : reduction _ _ |- _ => inversion H; subst end; try discriminate; eauto 7 using rtc_refl, rtc_one. Qed.
Lemma ipi_reduction : forall A B D, reduction (TIPi A B) D ->
  exists A' B', D = TIPi A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Proof. intros; match goal with H : reduction _ _ |- _ => inversion H; subst end; try discriminate; eauto 7 using rtc_refl, rtc_one. Qed.
Lemma isig_reduction : forall A B D, reduction (TISig A B) D ->
  exists A' B', D = TISig A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Proof. intros; match goal with H : reduction _ _ |- _ => inversion H; subst end; try discriminate; eauto 7 using rtc_refl, rtc_one. Qed.
Lemma ichoice_reduction : forall A B D, reduction (TIChoice A B) D ->
  exists A' B', D = TIChoice A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Proof. intros; match goal with H : reduction _ _ |- _ => inversion H; subst end; try discriminate; eauto 7 using rtc_refl, rtc_one. Qed.

Lemma variable_index_meaning : forall RI, candidate RI -> forall i RX F,
  RI i -> stable_indexed_family RI RX -> small_description RI (TIVar i) F ->
  predicate_equiv (RX i) (F RX).
Proof.
  intros RI CRI i RX F Hi HF HD.
  pose proof (candidate_normalizing CRI Hi) as HSi.
  destruct (normalize_full _ HSi) as [j [Rj Nj]].
  assert (Hj : RI j) by (eapply candidate_reducts; eassumption).
  assert (Hvar : small_description RI (TIVar i) (fun Y => Y j)).
  { eapply di_var.
    - now apply full_SN_ivar.
    - now apply red_star_TIVar.
    - intros u HU; inversion HU; subst; [discriminate|eapply Nj; eassumption].
    - exact Hj. }
  pose proof (small_description_unique _ _ _ _ _ _ Hvar HD (cv_refl _) RX) as HE.
  assert (HX : predicate_equiv (RX i) (RX j)).
  { apply (proj2 HF i j Hi Hj), reductions_conversion; exact Rj. }
  intro t; specialize (HX t); specialize (HE t); tauto.
Qed.
Lemma variable_description_meaning : forall RI, candidate RI -> forall i X RX F,
  RI i -> interpreted_family RI X RX -> small_description RI (TIVar i) F ->
  predicate_equiv (RX i) (F RX).
Proof.
  intros RI CRI i X RX F Hi HF HD; apply (variable_index_meaning RI CRI i RX F Hi);
    [now apply interpreted_family_stable with X|exact HD].
Qed.
Lemma interpretation_change_meaning : forall RI D F G RX T,
  small_description RI D F -> small_description RI D G ->
  small_interp T (F RX) -> small_interp T (G RX).
Proof.
  intros RI D F G RX T HF HG HT; eapply it_equiv; [exact HT|].
  exact (small_description_unique _ _ _ _ _ _ HF HG (cv_refl _) RX).
Qed.
Lemma interpreted_code_reduct : forall RI, candidate RI -> forall D D',
  small_code RI D -> interpretation_roots RI D -> rtc reduction D D' ->
  forall IT X RX, full_SN IT -> full_SN X -> interpreted_family RI X RX ->
  small_description RI D' (code_meaning RI D) /\
  small_interp (TInterp IT D' X) (code_meaning RI D RX).
Proof.
  intros RI CRI D D' HD HR HD' IT X RX HI HX HF; split.
  - eapply description_interp_reductions; [exact (small_code_meaning RI CRI D HD)|exact HD'].
  - eapply type_interp_reductions;
      [exact (interpretation_from_code_roots RI CRI D HD HR IT X RX HI HX HF)|].
    apply red_star_TInterp; [constructor|exact HD'|constructor].
Qed.

Theorem computable_interpretation_roots : forall RI, candidate RI -> forall D,
  small_code RI D -> interpretation_roots RI D.
Proof.
  intros RI CRI D HD; induction HD;
    intros Dout RD IT X RX HI HX HF F HDF v HV.
  - destruct (ivar_reductions _ _ RD) as [j [-> Rj]].
    cbn [root_step] in HV; inversion HV; subst v.
    assert (Hj : RI j) by (eapply candidate_reducts; eassumption).
    eapply it_equiv; [exact (HF j Hj)|].
    exact (variable_description_meaning RI CRI j X RX F Hj HF HDF).
  - pose proof (normal_reductions_identity _ _ one_description_normal RD) as HE; subst Dout.
    cbn [root_step] in HV; inversion HV; subst v.
    eapply interpretation_change_meaning; [|exact HDF|exact small_unit_interp].
    apply di_one; [apply normal_form_accessible, one_description_normal|constructor].
  - pose proof (normal_reductions_identity _ _ bot_description_normal RD) as HE; subst Dout.
    cbn [root_step] in HV; inversion HV; subst v.
    eapply interpretation_change_meaning; [|exact HDF|exact small_bottom_interp].
    apply di_bot; [apply normal_form_accessible, bot_description_normal|constructor].
  - destruct (reduces_binary TIProd iprod_reduction _ _ _ RD) as [A' [B' [-> [RA RB]]]].
    cbn [root_step] in HV; inversion HV; subst v.
    destruct (interpreted_code_reduct RI CRI A A' HD1 IHHD1 RA IT X RX HI HX HF) as [HDA HA].
    destruct (interpreted_code_reduct RI CRI B B' HD2 IHHD2 RB IT X RX HI HX HF) as [HDB HB].
    eapply interpretation_change_meaning with
      (F:=fun Y => dependent_pair (code_meaning RI A Y) (fun _ => code_meaning RI B Y));
      [|exact HDF|apply small_product_interp; [exact HA|exact HB]].
    eapply description_interp_prod_intro; eassumption.
  - destruct (reduces_binary TIPi ipi_reduction _ _ _ RD) as [A' [f' [-> [RA' Rf]]]].
    cbn [root_step] in HV; inversion HV; subst v.
    assert (HA' : small_interp A' RA) by (eapply type_interp_reductions; eassumption).
    assert (Hf' : full_SN f') by (exact (full_SN_reductions _ H0 _ Rf)).
    assert (HB : forall a, RA a ->
      small_description RI (TApp f' a) (code_meaning RI (TApp D a)) /\
      small_interp (TInterp IT (TApp f' a) X) (code_meaning RI (TApp D a) RX)).
    { intros a Ha; eapply interpreted_code_reduct;
        [exact CRI|exact (H1 a Ha)|exact (H2 a Ha)| |exact HI|exact HX|exact HF].
      apply red_star_TApp; [exact Rf|constructor]. }
    eapply interpretation_change_meaning with
      (F:=fun Y => dependent_function RA (fun a => code_meaning RI (TApp D a) Y)); [|exact HDF|].
    + eapply description_interp_pi_intro; [exact HA'|exact Hf'|].
      intros a Ha; exact (proj1 (HB a Ha)).
    + apply small_pi_interp; [exact HA'|].
      intros a Ha; rewrite instantiated_interpretation; exact (proj2 (HB a Ha)).
  - destruct (reduces_binary TISig isig_reduction _ _ _ RD) as [A' [f' [-> [RA' Rf]]]].
    cbn [root_step] in HV; inversion HV; subst v.
    assert (HA' : small_interp A' RA) by (eapply type_interp_reductions; eassumption).
    assert (Hf' : full_SN f') by (exact (full_SN_reductions _ H0 _ Rf)).
    assert (HB : forall a, RA a ->
      small_description RI (TApp f' a) (code_meaning RI (TApp D a)) /\
      small_interp (TInterp IT (TApp f' a) X) (code_meaning RI (TApp D a) RX)).
    { intros a Ha; eapply interpreted_code_reduct;
        [exact CRI|exact (H1 a Ha)|exact (H2 a Ha)| |exact HI|exact HX|exact HF].
      apply red_star_TApp; [exact Rf|constructor]. }
    eapply interpretation_change_meaning with
      (F:=fun Y => dependent_pair RA (fun a => code_meaning RI (TApp D a) Y)); [|exact HDF|].
    + eapply description_interp_sigma_intro; [exact HA'|exact Hf'|].
      intros a Ha; exact (proj1 (HB a Ha)).
    + apply small_sigma_interp; [exact HA'|].
      intros a Ha; rewrite instantiated_interpretation; exact (proj2 (HB a Ha)).
  - destruct (reduces_binary TIChoice ichoice_reduction _ _ _ RD) as [E' [f' [-> [RE' Rf]]]].
    cbn [root_step] in HV; inversion HV; subst v.
    assert (HE' : small_interp (TEnumT E') RE).
    { eapply type_interp_reductions; [exact H|now apply red_star_TEnumT]. }
    assert (Hf' : full_SN f') by (exact (full_SN_reductions _ H0 _ Rf)).
    assert (HB : forall a, RE a ->
      small_description RI (TApp f' a) (code_meaning RI (TApp D a)) /\
      small_interp (TInterp IT (TApp f' a) X) (code_meaning RI (TApp D a) RX)).
    { intros a Ha; eapply interpreted_code_reduct;
        [exact CRI|exact (H1 a Ha)|exact (H2 a Ha)| |exact HI|exact HX|exact HF].
      apply red_star_TApp; [exact Rf|constructor]. }
    eapply interpretation_change_meaning with
      (F:=fun Y => dependent_pair RE (fun a => code_meaning RI (TApp D a) Y)); [|exact HDF|].
    + eapply description_interp_choice_intro; [exact HE'|exact Hf'|].
      intros a Ha; exact (proj1 (HB a Ha)).
    + apply small_sigma_interp; [exact HE'|].
      intros a Ha; rewrite instantiated_interpretation; exact (proj2 (HB a Ha)).
  - eapply IHHD; [eapply rtc_step; eassumption|exact HI|exact HX|exact HF|exact HDF|exact HV].
  - inversion RD; subst.
    + destruct Dout; cbn [neutral root_step] in *; contradiction || discriminate.
    + exact (H1 y H2 Dout H3 IT X RX HI HX HF F HDF v HV).
Qed.

Theorem interpretation_computable : forall RI, candidate RI -> forall D,
  small_code RI D -> forall IT X RX, full_SN IT -> full_SN X -> interpreted_family RI X RX ->
  small_interp (TInterp IT D X) (code_meaning RI D RX).
Proof.
  intros RI CRI D HD; apply interpretation_from_code_roots;
    [exact CRI|exact HD|now apply computable_interpretation_roots].
Qed.
Theorem interpretation_computable_as : forall RI, candidate RI -> forall D F,
  small_code RI D -> small_description RI D F ->
  forall IT X RX, full_SN IT -> full_SN X -> interpreted_family RI X RX ->
  small_interp (TInterp IT D X) (F RX).
Proof.
  intros RI CRI D F HD HDF; apply interpretation_from_roots;
    [exact HDF|now apply computable_interpretation_roots].
Qed.

Print Assumptions interpretation_from_roots.
Print Assumptions computable_interpretation_roots.
Print Assumptions interpretation_computable.
Print Assumptions interpretation_computable_as.
