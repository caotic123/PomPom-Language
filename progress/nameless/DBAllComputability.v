(* Computability of types of recursive hypotheses. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBInterpretationComputability.
Import ListNotations Full.

Lemma small_type_canonical : forall A, reducible_type small_atom A ->
  small_interp A (type_elements small_atom A).
Proof.
  intros A H; apply type_interp_canonical;
    [exact small_atom_not_neutral|exact small_atom_not_pi|exact small_atom_not_sigma
    |intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)|exact H].
Qed.
Lemma interpreted_family_candidates : forall RI X RX,
  interpreted_family RI X RX -> Indexed.candidates RI RX.
Proof. intros RI X RX H i Hi; exact (small_type_candidate _ _ (H i Hi)). Qed.
Lemma description_family_stable : forall A f (F : term -> description_functor) RI,
  candidate A -> (forall a, A a -> small_description RI (TApp f a) (F a)) ->
  forall X, stable_family A (fun a => F a X).
Proof.
  intros A f F RI CA HF X a a' Ha HR.
  assert (Ha' : A a') by (eapply candidate_reduct; eassumption).
  eapply small_description_unique; [exact (HF a Ha)|exact (HF a' Ha')|].
  apply reductions_conversion, rtc_one; now apply red_TApp_a.
Qed.
Lemma dependent_pair_value : forall A B, candidate A ->
  (forall a, A a -> candidate (B a)) -> stable_family A B ->
  forall a b, dependent_pair A B (TPair a b) -> A a /\ B a b.
Proof.
  intros A B CA CB CS a b [_ [HA HB]].
  assert (Ha : A a) by (exact (candidate_reduct CA HA (@red_root (TFst (TPair a b)) a eq_refl))).
  split; [exact Ha|].
  apply (proj1 (CS _ _ HA (@red_root (TFst (TPair a b)) a eq_refl) b)).
  exact (candidate_reduct (CB _ HA) HB (@red_root (TSnd (TPair a b)) b eq_refl)).
Qed.

Definition hypothesis_family (RI : term -> Prop) (RX : payload_family) P :=
  forall i x, RI i -> RX i x -> reducible_type small_atom (TApp P (TPair i x)).
Lemma hypothesis_family_reductions : forall RI RX P,
  hypothesis_family RI RX P -> forall Q, rtc reduction P Q -> hypothesis_family RI RX Q.
Proof.
  intros RI RX P HP Q HR i x Hi Hx; destruct (HP i x Hi Hx) as [R HT]; exists R.
  eapply type_interp_reductions; [exact HT|apply red_star_TApp; [exact HR|constructor]].
Qed.
Definition all_roots RI D := forall D', rtc reduction D D' ->
  forall IT X RX P, full_SN IT -> full_SN X -> full_SN P ->
  stable_indexed_family RI RX -> hypothesis_family RI RX P ->
  forall F xs, small_description RI D' F -> F RX xs -> forall v,
  root_step (TIAll IT D' X xs P) = Some v -> reducible_type small_atom v.
Lemma all_roots_reductions : forall RI D, all_roots RI D ->
  forall E, rtc reduction D E -> all_roots RI E.
Proof. intros RI D HD E HR F HE; apply HD; eapply rtc_trans; eassumption. Qed.

Theorem all_from_roots : forall RI D F,
  small_description RI D F -> all_roots RI D ->
  forall IT X RX P xs, full_SN IT -> full_SN X -> full_SN P ->
  stable_indexed_family RI RX -> hypothesis_family RI RX P -> F RX xs ->
  reducible_type small_atom (TIAll IT D X xs P).
Proof.
  intros RI D F HD HR IT X RX P xs HI HX HP HF HQ Hxs.
  pose proof (proj1 HF) as CX.
  pose proof (small_description_candidate _ _ _ HD RX CX) as CF.
  apply computability_by_head_expansion; [apply reducible_type_candidate| | |].
  - cbn [term_children]; constructor; [exact HI|].
    constructor; [exact (description_interp_normalizing _ _ _ _ HD)|].
    constructor; [exact HX|].
    constructor; [exact (candidate_normalizing CF Hxs)|].
    constructor; [exact HP|constructor].
  - intros u HU; inversion HU; exact I.
  - intros u v HU HV; inversion HU; subst; inversion HV; subst.
    eapply HR; [eassumption| | | | | | | |eassumption].
    + eapply full_SN_reductions; [exact HI|eassumption].
    + eapply full_SN_reductions; [exact HX|eassumption].
    + eapply full_SN_reductions; [exact HP|eassumption].
    + exact HF.
    + eapply hypothesis_family_reductions; [exact HQ|eassumption].
    + eapply description_interp_reductions; [exact HD|eassumption].
    + eapply candidate_reducts; [exact CF|eassumption|exact Hxs].
Qed.

Lemma code_reduct_meaning : forall RI, candidate RI -> forall D D',
  small_code RI D -> rtc reduction D D' ->
  small_description RI D' (code_meaning RI D).
Proof.
  intros RI CRI D D' HD HR; eapply description_interp_reductions;
    [exact (small_code_meaning RI CRI D HD)|exact HR].
Qed.
Lemma all_reduced_code : forall RI, candidate RI -> forall D D',
  small_code RI D -> all_roots RI D -> rtc reduction D D' ->
  forall IT X RX P xs, full_SN IT -> full_SN X -> full_SN P ->
  stable_indexed_family RI RX -> hypothesis_family RI RX P -> code_meaning RI D RX xs ->
  reducible_type small_atom (TIAll IT D' X xs P).
Proof.
  intros RI CRI D D' HD HR HD' IT X RX P xs HI HX HP HF HQ Hxs.
  eapply all_from_roots; [exact (code_reduct_meaning RI CRI D D' HD HD')
    |eapply all_roots_reductions; eassumption|exact HI|exact HX|exact HP|exact HF|exact HQ|exact Hxs].
Qed.

Lemma small_type_product : forall A B,
  reducible_type small_atom A -> reducible_type small_atom B -> reducible_type small_atom (product A B).
Proof. intros A B [RA HA] [RB HB]; eexists; eapply small_product_interp; eassumption. Qed.

Theorem computable_all_roots : forall RI, candidate RI -> forall D,
  small_code RI D -> all_roots RI D.
Proof.
  intros RI CRI D HD; induction HD;
    intros Dout RD IT X RX P HI HX HP HF HQ F xs HDF Hxs v HV.
  - destruct (ivar_reductions _ _ RD) as [j [-> Rj]].
    cbn [root_step] in HV; inversion HV; subst v.
    assert (Hj : RI j) by (eapply candidate_reducts; eassumption).
    apply HQ; [exact Hj|].
    apply (variable_index_meaning RI CRI j RX F Hj HF HDF); exact Hxs.
  - pose proof (normal_reductions_identity _ _ one_description_normal RD) as HE; subst Dout.
    destruct xs; cbn [root_step] in HV; try discriminate; inversion HV; subst v.
    exists full_SN; exact small_unit_interp.
  - pose proof (normal_reductions_identity _ _ bot_description_normal RD) as HE; subst Dout.
    cbn [root_step] in HV; inversion HV; subst v.
    exists full_SN; exact small_unit_interp.
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
    apply small_type_product.
    + exact (all_reduced_code RI CRI A A' HD1 IHHD1 RA IT X RX P xs1 HI HX HP HF HQ Ha).
    + exact (all_reduced_code RI CRI B B' HD2 IHHD2 RB IT X RX P xs2 HI HX HP HF HQ Hb).
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
    exists (dependent_function RA (fun a => type_elements small_atom (TIAll IT (TApp f' a) X (TApp xs a) P))).
    apply small_pi_interp; [exact HA'|].
    intros a Ha; cbn [subst]; rewrite ?subst_lift_zero, ?lift_zero_id.
    apply small_type_canonical.
    eapply all_reduced_code; [exact CRI|exact (H1 a Ha)|exact (H2 a Ha)|
      |exact HI|exact HX|exact HP|exact HF|exact HQ|exact (proj2 Hfun a Ha)].
    apply red_star_TApp; [exact Rf|constructor].
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
    eapply all_reduced_code; [exact CRI|exact (H1 xs1 Ha)|exact (H2 xs1 Ha)|
      |exact HI|exact HX|exact HP|exact HF|exact HQ|exact Hb].
    apply red_star_TApp; [exact Rf|constructor].
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
    eapply all_reduced_code; [exact CRI|exact (H1 xs1 Ha)|exact (H2 xs1 Ha)|
      |exact HI|exact HX|exact HP|exact HF|exact HQ|exact Hb].
    apply red_star_TApp; [exact Rf|constructor].
  - eapply IHHD; [eapply rtc_step; eassumption|exact HI|exact HX|exact HP|exact HF|exact HQ|exact HDF|exact Hxs|exact HV].
  - inversion RD; subst.
    + destruct Dout; cbn [neutral root_step] in *; contradiction || discriminate.
    + exact (H1 y H2 Dout H3 IT X RX P HI HX HP HF HQ F xs HDF Hxs v HV).
Qed.

Theorem all_computable : forall RI, candidate RI -> forall D F,
  small_code RI D -> small_description RI D F ->
  forall IT X RX P xs, full_SN IT -> full_SN X -> full_SN P ->
  stable_indexed_family RI RX -> hypothesis_family RI RX P -> F RX xs ->
  reducible_type small_atom (TIAll IT D X xs P).
Proof.
  intros RI CRI D F HD HDF; eapply all_from_roots;
    [exact HDF|now apply computable_all_roots].
Qed.

Print Assumptions all_from_roots.
Print Assumptions computable_all_roots.
Print Assumptions all_computable.
