(* Dependent enumeration products in every universe level. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBCloseCaseComputability.
Import ListNotations Full.

Lemma calculus_sigma_interp : forall n A B RA RB,
  calculus_interp n A RA ->
  (forall a, RA a -> calculus_interp n (subst a 0 B) (RB a)) ->
  calculus_interp n (TSigma A B) (dependent_pair RA RB).
Proof.
  intros; eapply type_interp_sigma_intro.
  - apply level_atom_candidate; [exact primitive_candidate|apply universe_levels_candidates].
  - apply level_atom_not_neutral; exact primitive_not_neutral.
  - apply level_atom_not_pi; exact primitive_not_pi.
  - apply level_atom_not_sigma; exact primitive_not_sigma.
  - apply level_atom_unique; [exact primitive_not_sort|exact primitive_unique].
  - eassumption.
  - eassumption.
Qed.
Lemma calculus_product_interp : forall n A B RA RB,
  calculus_interp n A RA -> calculus_interp n B RB ->
  calculus_interp n (product A B) (dependent_pair RA (fun _ => RB)).
Proof.
  intros n A B RA RB HA HB; apply calculus_sigma_interp; [exact HA|].
  intros a Ha; now rewrite subst_lift_zero.
Qed.
Lemma calculus_product_type : forall n A B,
  calculus_type n A -> calculus_type n B -> calculus_type n (product A B).
Proof. intros n A B [RA HA] [RB HB]; eexists; eapply calculus_product_interp; eassumption. Qed.

Definition enum_tail_family P := TLam (TApp (lift 1 0 P) (TESucc (TVar 0))).
Lemma enum_tail_subst : forall P e,
  subst e 0 (TApp (lift 1 0 P) (TESucc (TVar 0))) = TApp P (TESucc e).
Proof. intros; cbn [subst]; now rewrite subst_lift_zero, lift_zero_id. Qed.
Lemma enum_tail_computable : forall E P R, candidate R ->
  (forall e, enum_elements E e -> R (TApp P (TESucc e))) ->
  dependent_function (enum_elements E) (fun _ => R) (enum_tail_family P).
Proof.
  intros E P R CR HF; apply dependent_lambda_computable;
    [apply enum_elements_candidate|intros; exact CR|intros a b Ha HR t; tauto|].
  intros e He; rewrite enum_tail_subst; now apply HF.
Qed.
Definition enum_family n E P := forall e, enum_elements E e -> calculus_type n (TApp P e).
Lemma enum_family_reductions : forall n E P, enum_family n E P ->
  forall E' P', rtc reduction E E' -> rtc reduction P P' -> enum_family n E' P'.
Proof.
  intros n E P HF E' P' RE RP e He.
  eapply candidate_reducts; [apply calculus_type_candidate| |apply HF].
  - apply red_star_TApp; [exact RP|constructor].
  - apply (enum_elements_conversion _ _ (reductions_conversion _ _ RE)); exact He.
Qed.
Lemma enum_tail_family_computable : forall n tag E P, full_SN tag -> full_SN E ->
  enum_family n (TConsE tag E) P ->
  full_SN (enum_tail_family P) /\ enum_family n E (enum_tail_family P).
Proof.
  intros n tag E P HT HE HF; apply enum_tail_computable; [apply calculus_type_candidate|].
  intros e He; apply HF; now apply enum_succ_computable.
Qed.
Lemma cons_enum_reductions : forall tag E t, rtc reduction (TConsE tag E) t ->
  exists tag' E', t = TConsE tag' E' /\ rtc reduction tag tag' /\ rtc reduction E E'.
Proof.
  apply reduces_binary; intros tag E t H; destruct (cons_enum_reduction_components _ _ _ H)
    as [[tag' [HR ->]]|[E' [HR ->]]]; eauto 6 using rtc_refl, rtc_one.
Qed.
Definition epi_roots E := forall E', rtc reduction E E' -> forall n k P,
  full_SN P -> enum_family n E' P -> forall v,
  root_step (TEPi k E' P) = Some v -> calculus_type n v.
Lemma epi_roots_reductions : forall E, epi_roots E -> forall E',
  rtc reduction E E' -> epi_roots E'.
Proof. intros E H E' HR E'' HR'; apply H; eapply rtc_trans; eassumption. Qed.
Lemma epi_from_roots : forall E, full_SN E -> epi_roots E -> forall n k P,
  full_SN P -> enum_family n E P -> calculus_type n (TEPi k E P).
Proof.
  intros E HE HR n k P HP HF; apply computability_by_head_expansion;
    [apply calculus_type_candidate| | |].
  - cbn [term_children]; constructor; [exact HE|constructor; [exact HP|constructor]].
  - intros t Ht; inversion Ht; exact I.
  - intros t v Ht Hv; inversion Ht; subst; inversion Hv; subst.
    eapply HR; [eassumption| | |eassumption].
    + eapply full_SN_reductions; eassumption.
    + eapply enum_family_reductions; eassumption.
Qed.
Theorem computable_epi_roots : forall E, enumeration_computable E -> epi_roots E.
Proof.
  intros E H; induction H; intros Eout RE n k P HP HF v HV.
  - pose proof (normal_reductions_identity _ _ nil_enum_normal RE); subst Eout.
    cbn [root_step] in HV; inversion HV; subst v.
    exists full_SN; apply calculus_unit_type.
  - destruct (cons_enum_reductions _ _ _ RE) as [tag' [E' [-> [RT RE']]]].
    cbn [root_step] in HV; inversion HV; subst v.
    pose proof (full_SN_reductions _ H _ RT) as HT'.
    pose proof (full_SN_reductions _ (enumeration_computable_normalizing _ H0) _ RE') as HE'.
    destruct (enum_tail_family_computable n tag' E' P HT' HE' HF) as [HS HFtail].
    apply calculus_product_type.
    + apply HF; now apply enum_zero_computable.
    + apply epi_from_roots; [exact HE'|eapply epi_roots_reductions; eassumption|exact HS|exact HFtail].
  - eapply IHenumeration_computable; [eapply rtc_step; eassumption|exact HP|exact HF|exact HV].
  - inversion RE; subst.
    + destruct Eout; cbn [neutral root_step] in *; contradiction || discriminate.
    + eapply H1; eassumption.
Qed.
Theorem epi_computable : forall E, enumeration_computable E -> forall n k P,
  full_SN P -> enum_family n E P -> calculus_type n (TEPi k E P).
Proof.
  intros E HE; apply epi_from_roots;
    [now apply enumeration_computable_normalizing|now apply computable_epi_roots].
Qed.

Print Assumptions epi_computable.
