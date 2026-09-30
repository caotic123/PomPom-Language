(* Computability of the generic constructor of recursive hypotheses. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBAllComputability.
Import ListNotations Full.

Definition small_value t A := exists R, small_interp A R /\ R t.
Lemma small_value_member : forall t A R,
  small_value t A -> small_interp A R -> R t.
Proof.
  intros t A R [S [HS Ht]] HR; apply (small_interp_unique _ _ _ _ HS HR (cv_refl _) t); exact Ht.
Qed.
Lemma small_value_reductions : forall t A, small_value t A ->
  forall u, rtc reduction t u -> small_value u A.
Proof.
  intros t A [R [HR Ht]] u HU; exists R; split; [exact HR|].
  exact (candidate_reducts _ (small_type_candidate _ _ HR) _ _ HU Ht).
Qed.
Lemma small_value_type_reductions : forall t A, small_value t A ->
  forall B, rtc reduction A B -> small_value t B.
Proof.
  intros t A [R [HR Ht]] B HB; exists R; split; [eapply type_interp_reductions; eassumption|exact Ht].
Qed.
Lemma small_value_unit : small_value TUnit TUnitT.
Proof.
  exists full_SN; split; [exact small_unit_interp|].
  apply normal_form_accessible; intros u H; inversion H; discriminate.
Qed.
Lemma interpreted_codomain_stable : forall A B RB, candidate A ->
  (forall a, A a -> small_interp (subst a 0 B) (RB a)) -> stable_family A RB.
Proof.
  intros A B RB CA HB a a' Ha HR.
  assert (Ha' : A a') by (eapply candidate_reduct; eassumption).
  eapply small_interp_unique; [exact (HB a Ha)|exact (HB a' Ha')|].
  apply reductions_conversion; now apply reduction_subst_argument.
Qed.

Definition hypothesis_method RI RX P h := full_SN h /\
  forall i x, RI i -> RX i x -> small_value (TApp (TApp h i) x) (TApp P (TPair i x)).
Lemma hypothesis_method_reductions : forall RI RX P h,
  hypothesis_method RI RX P h -> forall P' h',
  rtc reduction P P' -> rtc reduction h h' -> hypothesis_method RI RX P' h'.
Proof.
  intros RI RX P h [HS HM] P' h' RP Rh; split; [exact (full_SN_reductions _ HS _ Rh)|].
  intros i x Hi Hx; eapply small_value_type_reductions.
  - eapply small_value_reductions; [exact (HM i x Hi Hx)|].
    apply red_star_TApp; [apply red_star_TApp; [exact Rh|constructor]|constructor].
  - apply red_star_TApp; [exact RP|constructor].
Qed.

Definition hyps_roots RI D := forall D', rtc reduction D D' ->
  forall IT X RX P h, full_SN IT -> full_SN X -> full_SN P ->
  stable_indexed_family RI RX -> hypothesis_family RI RX P -> hypothesis_method RI RX P h ->
  forall F xs R, small_description RI D' F -> F RX xs ->
  small_interp (TIAll IT D' X xs P) R -> forall v,
  root_step (THyps IT D' X P h xs) = Some v -> R v.
Lemma hyps_roots_reductions : forall RI D, hyps_roots RI D ->
  forall E, rtc reduction D E -> hyps_roots RI E.
Proof. intros RI D HD E HR F HE; apply HD; eapply rtc_trans; eassumption. Qed.

Theorem hyps_from_roots : forall RI D F,
  small_description RI D F -> hyps_roots RI D ->
  forall IT X RX P h xs R, full_SN IT -> full_SN X -> full_SN P ->
  stable_indexed_family RI RX -> hypothesis_family RI RX P -> hypothesis_method RI RX P h ->
  F RX xs -> small_interp (TIAll IT D X xs P) R -> R (THyps IT D X P h xs).
Proof.
  intros RI D F HD HR IT X RX P h xs R HI HX HP HF HQ HM Hxs HT.
  pose proof (proj1 HF) as CX.
  pose proof (small_description_candidate _ _ _ HD RX CX) as CF.
  apply computability_by_head_expansion; [exact (small_type_candidate _ _ HT)| | |].
  - cbn [term_children]; constructor; [exact HI|].
    constructor; [exact (description_interp_normalizing _ _ _ _ HD)|].
    constructor; [exact HX|].
    constructor; [exact HP|].
    constructor; [exact (proj1 HM)|].
    constructor; [exact (candidate_normalizing CF Hxs)|constructor].
  - intros u HU; inversion HU; exact I.
  - intros u v HU HV; inversion HU; subst; inversion HV; subst.
    eapply HR; [eassumption| | | | | | | | | |eassumption].
    + eapply full_SN_reductions; [exact HI|eassumption].
    + eapply full_SN_reductions; [exact HX|eassumption].
    + eapply full_SN_reductions; [exact HP|eassumption].
    + exact HF.
    + eapply hypothesis_family_reductions; [exact HQ|eassumption].
    + eapply hypothesis_method_reductions; [exact HM|eassumption|eassumption].
    + eapply description_interp_reductions; [exact HD|eassumption].
    + eapply candidate_reducts; [exact CF|eassumption|exact Hxs].
    + eapply type_interp_reductions; [exact HT|].
      apply red_star_TIAll; assumption.
Qed.

Lemma hyps_reduced_code : forall RI, candidate RI -> forall D D',
  small_code RI D -> hyps_roots RI D -> rtc reduction D D' ->
  forall IT X RX P h xs R, full_SN IT -> full_SN X -> full_SN P ->
  stable_indexed_family RI RX -> hypothesis_family RI RX P -> hypothesis_method RI RX P h ->
  code_meaning RI D RX xs -> small_interp (TIAll IT D' X xs P) R ->
  R (THyps IT D' X P h xs).
Proof.
  intros RI CRI D D' HD HR HD' IT X RX P h xs R HI HX HP HF HQ HM Hxs HT.
  eapply hyps_from_roots; [exact (code_reduct_meaning RI CRI D D' HD HD')
    |eapply hyps_roots_reductions; eassumption|exact HI|exact HX|exact HP|exact HF|exact HQ|exact HM|exact Hxs|exact HT].
Qed.

Lemma small_value_at_all_root : forall IT D X xs P R v,
  small_interp (TIAll IT D X xs P) R -> forall T,
  root_step (TIAll IT D X xs P) = Some T -> small_value v T -> R v.
Proof.
  intros IT D X xs P R v HR T HT Hv; eapply small_value_member; [exact Hv|].
  eapply type_interp_reductions; [exact HR|apply rtc_one, red_root; exact HT].
Qed.

Theorem computable_hyps_roots : forall RI, candidate RI -> forall D,
  small_code RI D -> hyps_roots RI D.
Proof.
  intros RI CRI D HD; induction HD;
    intros Dout RD IT X RX P h HI HX HP HF HQ HM F xs R HDF Hxs HT v HV.
  - destruct (ivar_reductions _ _ RD) as [j [-> Rj]].
    cbn [root_step] in HV; inversion HV; subst v.
    assert (Hj : RI j) by (eapply candidate_reducts; eassumption).
    assert (Hjxs : RX j xs) by (apply (variable_index_meaning RI CRI j RX F Hj HF HDF); exact Hxs).
    eapply small_value_at_all_root; [exact HT|reflexivity|].
    exact (proj2 HM j xs Hj Hjxs).
  - pose proof (normal_reductions_identity _ _ one_description_normal RD) as HE; subst Dout.
    destruct xs; cbn [root_step] in HV; try discriminate; inversion HV; subst v.
    eapply small_value_at_all_root; [exact HT|reflexivity|exact small_value_unit].
  - pose proof (normal_reductions_identity _ _ bot_description_normal RD) as HE; subst Dout.
    cbn [root_step] in HV; inversion HV; subst v.
    eapply small_value_at_all_root; [exact HT|reflexivity|exact small_value_unit].
  - destruct (reduces_binary TIProd iprod_reduction _ _ _ RD) as [A' [B' [-> [RA RB]]]].
    destruct xs; cbn [root_step] in HV; try discriminate; inversion HV; subst v.
    pose proof (code_reduct_meaning RI CRI A A' HD1 RA) as HDA.
    pose proof (code_reduct_meaning RI CRI B B' HD2 RB) as HDB.
    pose proof (proj1 HF) as CX.
    pose proof (small_description_candidate _ _ _ HDA RX CX) as CA.
    pose proof (small_description_candidate _ _ _ HDB RX CX) as CB.
    assert (HDprod : small_description RI (TIProd A' B')
      (fun Y => dependent_pair (code_meaning RI A Y) (fun _ => code_meaning RI B Y)))
      by (eapply description_interp_prod_intro; eassumption).
    assert (Hpair : dependent_pair (code_meaning RI A RX) (fun _ => code_meaning RI B RX) (TPair xs1 xs2)).
    { apply (small_description_unique _ _ _ _ _ _ HDF HDprod (cv_refl _) RX); exact Hxs. }
    destruct (dependent_pair_value _ _ CA (fun _ _ => CB) (fun _ _ _ _ _ => iff_refl _) _ _ Hpair) as [Ha Hb].
    pose proof (small_type_canonical _ (all_reduced_code RI CRI A A' HD1
      (computable_all_roots RI CRI A HD1) RA IT X RX P xs1 HI HX HP HF HQ Ha)) as HAT.
    pose proof (small_type_canonical _ (all_reduced_code RI CRI B B' HD2
      (computable_all_roots RI CRI B HD2) RB IT X RX P xs2 HI HX HP HF HQ Hb)) as HBT.
    eapply small_value_at_all_root; [exact HT|reflexivity|].
    exists (dependent_pair (type_elements small_atom (TIAll IT A' X xs1 P))
      (fun _ => type_elements small_atom (TIAll IT B' X xs2 P))); split.
    + now apply small_product_interp.
    + apply dependent_pair_computable.
      * exact (small_type_candidate _ _ HAT).
      * intros; exact (small_type_candidate _ _ HBT).
      * intros a a' Haa HR t; tauto.
      * exact (hyps_reduced_code RI CRI A A' HD1 IHHD1 RA IT X RX P h xs1 _ HI HX HP HF HQ HM Ha HAT).
      * exact (hyps_reduced_code RI CRI B B' HD2 IHHD2 RB IT X RX P h xs2 _ HI HX HP HF HQ HM Hb HBT).
  - destruct (reduces_binary TIPi ipi_reduction _ _ _ RD) as [A' [f' [-> [RA' Rf]]]].
    cbn [root_step] in HV; inversion HV; subst v.
    assert (HA' : small_interp A' RA) by (eapply type_interp_reductions; eassumption).
    assert (Hf' : full_SN f') by (exact (full_SN_reductions _ H0 _ Rf)).
    assert (HB : forall a, RA a -> small_description RI (TApp f' a) (code_meaning RI (TApp D a))).
    { intros a Ha; eapply code_reduct_meaning; [exact CRI|exact (H1 a Ha)|].
      apply red_star_TApp; [exact Rf|constructor]. }
    assert (HDpi : small_description RI (TIPi A' f')
      (fun Y => dependent_function RA (fun a => code_meaning RI (TApp D a) Y)))
      by (eapply description_interp_pi_intro; eassumption).
    assert (Hfun : dependent_function RA (fun a => code_meaning RI (TApp D a) RX) xs).
    { apply (small_description_unique _ _ _ _ _ _ HDF HDpi (cv_refl _) RX); exact Hxs. }
    set (Bty := TIAll (lift 1 0 IT) (TApp (lift 1 0 f') (TVar 0))
      (lift 1 0 X) (TApp (lift 1 0 xs) (TVar 0)) (lift 1 0 P)).
    set (RB := fun a => type_elements small_atom (TIAll IT (TApp f' a) X (TApp xs a) P)).
    assert (HBT : forall a, RA a -> small_interp (subst a 0 Bty) (RB a)).
    { intros a Ha; unfold Bty; cbn [subst]; rewrite ?subst_lift_zero, ?lift_zero_id.
      apply small_type_canonical; eapply all_reduced_code;
        [exact CRI|exact (H1 a Ha)|exact (computable_all_roots RI CRI _ (H1 a Ha))|
        |exact HI|exact HX|exact HP|exact HF|exact HQ|exact (proj2 Hfun a Ha)].
      apply red_star_TApp; [exact Rf|constructor]. }
    pose proof (small_type_candidate _ _ HA') as CA.
    eapply small_value_at_all_root with (T:=TPi A' Bty); [exact HT|reflexivity|].
    exists (dependent_function RA RB); split; [now apply small_pi_interp|].
    apply dependent_lambda_computable.
    + exact CA.
    + intros a Ha; exact (small_type_candidate _ _ (HBT a Ha)).
    + exact (interpreted_codomain_stable RA Bty RB CA HBT).
    + intros a Ha; cbn [subst]; rewrite ?subst_lift_zero, ?lift_zero_id.
      eapply hyps_reduced_code; [exact CRI|exact (H1 a Ha)|exact (H2 a Ha)|
        |exact HI|exact HX|exact HP|exact HF|exact HQ|exact HM|exact (proj2 Hfun a Ha)|].
      * apply red_star_TApp; [exact Rf|constructor].
      * specialize (HBT a Ha); unfold Bty in HBT; cbn [subst] in HBT.
        now rewrite ?subst_lift_zero, ?lift_zero_id in HBT.
  - destruct (reduces_binary TISig isig_reduction _ _ _ RD) as [A' [f' [-> [RA' Rf]]]].
    destruct xs; cbn [root_step] in HV; try discriminate; inversion HV; subst v.
    assert (HA' : small_interp A' RA) by (eapply type_interp_reductions; eassumption).
    assert (Hf' : full_SN f') by (exact (full_SN_reductions _ H0 _ Rf)).
    assert (HB : forall a, RA a -> small_description RI (TApp f' a) (code_meaning RI (TApp D a))).
    { intros a Ha; eapply code_reduct_meaning; [exact CRI|exact (H1 a Ha)|].
      apply red_star_TApp; [exact Rf|constructor]. }
    assert (HDsigma : small_description RI (TISig A' f')
      (fun Y => dependent_pair RA (fun a => code_meaning RI (TApp D a) Y)))
      by (eapply description_interp_sigma_intro; eassumption).
    assert (Hpair : dependent_pair RA (fun a => code_meaning RI (TApp D a) RX) (TPair xs1 xs2)).
    { apply (small_description_unique _ _ _ _ _ _ HDF HDsigma (cv_refl _) RX); exact Hxs. }
    pose proof (small_type_candidate _ _ HA') as CA.
    pose proof (proj1 HF) as CX.
    destruct (dependent_pair_value _ _ CA
      (fun a Ha => small_description_candidate _ _ _ (HB a Ha) RX CX)
      (description_family_stable _ _ _ _ CA HB RX) _ _ Hpair) as [Ha Hb].
    eapply hyps_reduced_code; [exact CRI|exact (H1 xs1 Ha)|exact (H2 xs1 Ha)|
      |exact HI|exact HX|exact HP|exact HF|exact HQ|exact HM|exact Hb|].
    + apply red_star_TApp; [exact Rf|constructor].
    + eapply type_interp_reductions; [exact HT|apply rtc_one, red_root; reflexivity].
  - destruct (reduces_binary TIChoice ichoice_reduction _ _ _ RD) as [E' [f' [-> [RE' Rf]]]].
    destruct xs; cbn [root_step] in HV; try discriminate; inversion HV; subst v.
    assert (HE' : small_interp (TEnumT E') RE).
    { eapply type_interp_reductions; [exact H|now apply red_star_TEnumT]. }
    assert (Hf' : full_SN f') by (exact (full_SN_reductions _ H0 _ Rf)).
    assert (HB : forall a, RE a -> small_description RI (TApp f' a) (code_meaning RI (TApp D a))).
    { intros a Ha; eapply code_reduct_meaning; [exact CRI|exact (H1 a Ha)|].
      apply red_star_TApp; [exact Rf|constructor]. }
    assert (HDchoice : small_description RI (TIChoice E' f')
      (fun Y => dependent_pair RE (fun a => code_meaning RI (TApp D a) Y)))
      by (eapply description_interp_choice_intro; eassumption).
    assert (Hpair : dependent_pair RE (fun a => code_meaning RI (TApp D a) RX) (TPair xs1 xs2)).
    { apply (small_description_unique _ _ _ _ _ _ HDF HDchoice (cv_refl _) RX); exact Hxs. }
    pose proof (small_type_candidate _ _ HE') as CA.
    pose proof (proj1 HF) as CX.
    destruct (dependent_pair_value _ _ CA
      (fun a Ha => small_description_candidate _ _ _ (HB a Ha) RX CX)
      (description_family_stable _ _ _ _ CA HB RX) _ _ Hpair) as [Ha Hb].
    eapply hyps_reduced_code; [exact CRI|exact (H1 xs1 Ha)|exact (H2 xs1 Ha)|
      |exact HI|exact HX|exact HP|exact HF|exact HQ|exact HM|exact Hb|].
    + apply red_star_TApp; [exact Rf|constructor].
    + eapply type_interp_reductions; [exact HT|apply rtc_one, red_root; reflexivity].
  - eapply IHHD; [eapply rtc_step; eassumption|exact HI|exact HX|exact HP|exact HF|exact HQ|exact HM|exact HDF|exact Hxs|exact HT|exact HV].
  - inversion RD; subst.
    + destruct Dout; cbn [neutral root_step] in *; contradiction || discriminate.
    + exact (H1 y H2 Dout H3 IT X RX P h HI HX HP HF HQ HM F xs R HDF Hxs HT v HV).
Qed.

Theorem hyps_computable : forall RI, candidate RI -> forall D F,
  small_code RI D -> small_description RI D F ->
  forall IT X RX P h xs R, full_SN IT -> full_SN X -> full_SN P ->
  stable_indexed_family RI RX -> hypothesis_family RI RX P -> hypothesis_method RI RX P h ->
  F RX xs -> small_interp (TIAll IT D X xs P) R -> R (THyps IT D X P h xs).
Proof.
  intros RI CRI D F HD HDF; apply hyps_from_roots;
    [exact HDF|now apply computable_hyps_roots].
Qed.

Print Assumptions hyps_from_roots.
Print Assumptions computable_hyps_roots.
Print Assumptions hyps_computable.
