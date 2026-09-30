From Stdlib Require Import List Arith Bool Lia.
Require Export FullNormalFormsWork FullReducibilityWork.
Import Full.

Lemma conversion_to_normal : forall A B n,
  full_SN B -> conv A B -> rtc reduction A n -> normal_form n ->
  rtc reduction B n.
Proof.
  intros A B n HB HC HA HN; destruct (normalize_full _ HB) as [m [Hm HM]].
  assert (n = m) by (eapply normal_forms_join; eassumption).
  now subst m.
Qed.
Lemma reduction_subst_argument : forall a a', reduction a a' -> forall b k,
  rtc reduction (subst a k b) (subst a' k b).
Proof.
  intros a a' H b k; destruct (reduction_parallel _ _ H) as [HP|HE].
  - apply pstep_reductions, pstep_subst; [apply pstep_refl|exact HP].
  - apply epstep_reductions, epstep_subst; [apply epstep_refl|exact HE].
Qed.

Section TypeInterpretation.
Variable atom : term -> (term -> Prop) -> Prop.
Hypothesis atom_candidate : forall n R, atom n R -> candidate R.
Hypothesis atom_not_neutral : forall n R, atom n R -> ~ neutral n.
Hypothesis atom_not_pi : forall A B R, ~ atom (TPi A B) R.
Hypothesis atom_not_sigma : forall A B R, ~ atom (TSigma A B) R.
Hypothesis atom_unique : forall n R S,
  atom n R -> atom n S -> predicate_equiv R S.

Inductive type_interp : term -> (term -> Prop) -> Prop :=
| it_neutral : forall A n,
    full_SN A -> rtc reduction A n -> normal_form n -> neutral n ->
    type_interp A full_SN
| it_atom : forall A n R,
    full_SN A -> rtc reduction A n -> normal_form n -> atom n R ->
    type_interp A R
| it_pi : forall A U V RA RB,
    full_SN A -> rtc reduction A (TPi U V) -> normal_form (TPi U V) ->
    type_interp U RA -> (forall a, RA a -> type_interp (subst a 0 V) (RB a)) ->
    type_interp A (dependent_function RA RB)
| it_sigma : forall A U V RA RB,
    full_SN A -> rtc reduction A (TSigma U V) -> normal_form (TSigma U V) ->
    type_interp U RA -> (forall a, RA a -> type_interp (subst a 0 V) (RB a)) ->
    type_interp A (dependent_pair RA RB)
| it_equiv : forall A R S,
    type_interp A R -> predicate_equiv R S -> type_interp A S.

Lemma type_interp_normalizing : forall A R, type_interp A R -> full_SN A.
Proof. intros A R H; induction H; assumption. Qed.
Lemma type_interp_conversion : forall A R, type_interp A R ->
  forall B, full_SN B -> conv A B -> type_interp B R.
Proof.
  intros A R H; induction H; intros BB HB HC.
  - eapply it_neutral; [exact HB|eapply conversion_to_normal; eassumption|eassumption|eassumption].
  - eapply it_atom; [exact HB|eapply conversion_to_normal; eassumption|eassumption|eassumption].
  - eapply it_pi; [exact HB|eapply conversion_to_normal; eassumption|eassumption|eassumption|eassumption].
  - eapply it_sigma; [exact HB|eapply conversion_to_normal; eassumption|eassumption|eassumption|eassumption].
  - eapply it_equiv; [eapply IHtype_interp; eassumption|eassumption].
Qed.

Lemma type_interp_unique : forall A R, type_interp A R ->
  forall B S, type_interp B S -> conv A B -> predicate_equiv R S.
Proof.
  intros A R HA; induction HA; intros BB SS HB HC.
  all: try solve [intro t; specialize (IHHA _ _ HB HC t); specialize (H t); tauto].
  all: induction HB.
  all: try solve [match goal with
    IH : conv ?A ?B -> predicate_equiv ?R ?S,
    HE : predicate_equiv ?S ?S', HC : conv ?A ?B |- predicate_equiv ?R ?S' =>
    intro t; pose proof (IH HC t); pose proof (HE t); tauto end].
  all: try match goal with
    HL : rtc reduction ?A ?n, HNL : normal_form ?n,
    HR : rtc reduction ?B ?m, HNR : normal_form ?m,
    HC : conv ?A ?B |- _ =>
    let HE := fresh "HE" in
    assert (HE : n = m) by (eapply normal_forms_join; eassumption);
    inversion HE; subst; try clear HE
  end.
  all: try solve [cbn [neutral] in *; contradiction].
  all: try solve [exfalso; eapply atom_not_neutral; eassumption].
  all: try solve [exfalso; eapply atom_not_pi; eassumption].
  all: try solve [exfalso; eapply atom_not_sigma; eassumption].
  all: try solve [intro t; tauto].
  all: try solve [eapply atom_unique; eassumption].
  all: try solve [eapply dependent_function_equiv;
    [eapply IHHA; [eassumption|apply cv_refl]|];
    intros a Ha; eapply H3; [exact Ha| |apply cv_refl];
    apply H7; apply (IHHA _ _ HB (cv_refl _) a); exact Ha].
  all: try solve [eapply dependent_pair_equiv;
    [eapply IHHA; [eassumption|apply cv_refl]|];
    intros a Ha; eapply H3; [exact Ha| |apply cv_refl];
    apply H7; apply (IHHA _ _ HB (cv_refl _) a); exact Ha].
Qed.

Lemma type_interp_reductions : forall A R, type_interp A R ->
  forall B, rtc reduction A B -> type_interp B R.
Proof.
  intros A R HA B HR; apply (type_interp_conversion _ _ HA);
    [eapply full_SN_reductions; [eapply type_interp_normalizing; exact HA|exact HR]
    |exact (reductions_conversion _ _ HR)].
Qed.

Lemma type_interp_candidate : forall A R, type_interp A R -> candidate R.
Proof.
  intros A R H; induction H.
  - exact normalizing_candidate.
  - now apply atom_candidate with n.
  - apply dependent_function_candidate; [exact IHtype_interp|exact H4|].
    intros a a' Ha HR t.
    assert (Ha' : RA a') by (eapply candidate_reduct; eassumption).
    apply (type_interp_unique _ _ (H3 a Ha) _ _ (H3 a' Ha')).
    apply reductions_conversion; now apply reduction_subst_argument.
  - apply dependent_pair_candidate; [exact IHtype_interp|exact H4|].
    intros a a' Ha HR t.
    assert (Ha' : RA a') by (eapply candidate_reduct; eassumption).
    apply (type_interp_unique _ _ (H3 a Ha) _ _ (H3 a' Ha')).
    apply reductions_conversion; now apply reduction_subst_argument.
  - eapply candidate_equiv; eassumption.
Qed.

Definition reducible_type A := exists R, type_interp A R.
Theorem reducible_type_candidate : candidate reducible_type.
Proof.
  constructor.
  - intros A [R HR]; exact (type_interp_normalizing _ _ HR).
  - intros A B [R HR] H; exists R; apply (type_interp_reductions _ _ HR).
    now apply rtc_one.
  - intros A HN HR.
    assert (HS : full_SN A).
    { constructor; intros B HB; destruct (HR B HB) as [R HBR].
      exact (type_interp_normalizing _ _ HBR). }
    destruct (full_next A) as [B|] eqn:HE.
    + pose proof (full_next_sound _ _ HE) as HAB.
      destruct (HR B HAB) as [R HBR]; exists R.
      apply (type_interp_conversion _ _ HBR _ HS), cv_sym.
      apply reductions_conversion, rtc_one; exact HAB.
    + exists full_SN; eapply it_neutral;
        [exact HS|constructor|exact (full_next_complete _ HE)|exact HN].
Qed.

Definition type_elements A t := forall R, type_interp A R -> R t.
Lemma type_elements_equiv : forall A R, type_interp A R ->
  predicate_equiv R (type_elements A).
Proof.
  intros A R HR t; split.
  - intros H S HS; apply (type_interp_unique _ _ HR _ _ HS (cv_refl _) t); exact H.
  - intros H; exact (H R HR).
Qed.
Lemma type_interp_canonical : forall A, reducible_type A ->
  type_interp A (type_elements A).
Proof.
  intros A [R HR]; eapply it_equiv; [exact HR|exact (type_elements_equiv _ _ HR)].
Qed.
Lemma type_elements_candidate : forall A, reducible_type A -> candidate (type_elements A).
Proof. intros A H; exact (type_interp_candidate _ _ (type_interp_canonical _ H)). Qed.

Lemma type_interp_pi_intro : forall U V RA RB,
  type_interp U RA -> (forall a, RA a -> type_interp (subst a 0 V) (RB a)) ->
  type_interp (TPi U V) (dependent_function RA RB).
Proof.
  intros U V RA RB HU HV.
  pose proof (type_interp_normalizing _ _ HU) as HSU.
  pose proof (candidate_variable _ (type_interp_candidate _ _ HU) 0) as HX.
  pose proof (full_SN_subst_reflection V (TVar 0) 0
    (type_interp_normalizing _ _ (HV _ HX))) as HSV.
  destruct (normalize_full _ HSU) as [U' [RU NU]].
  destruct (normalize_full _ HSV) as [V' [RV NV]].
  eapply it_pi with (U:=U') (V:=V').
  - now apply full_SN_pi.
  - now apply red_star_TPi.
  - now apply normal_form_pi.
  - eapply type_interp_reductions; eassumption.
  - intros a HA; eapply type_interp_reductions; [exact (HV a HA)|].
    now apply reductions_subst.
Qed.
Lemma type_interp_sigma_intro : forall U V RA RB,
  type_interp U RA -> (forall a, RA a -> type_interp (subst a 0 V) (RB a)) ->
  type_interp (TSigma U V) (dependent_pair RA RB).
Proof.
  intros U V RA RB HU HV.
  pose proof (type_interp_normalizing _ _ HU) as HSU.
  pose proof (candidate_variable _ (type_interp_candidate _ _ HU) 0) as HX.
  pose proof (full_SN_subst_reflection V (TVar 0) 0
    (type_interp_normalizing _ _ (HV _ HX))) as HSV.
  destruct (normalize_full _ HSU) as [U' [RU NU]].
  destruct (normalize_full _ HSV) as [V' [RV NV]].
  eapply it_sigma with (U:=U') (V:=V').
  - now apply full_SN_sigma.
  - now apply red_star_TSigma.
  - now apply normal_form_sigma.
  - eapply type_interp_reductions; eassumption.
  - intros a HA; eapply type_interp_reductions; [exact (HV a HA)|].
    now apply reductions_subst.
Qed.
End TypeInterpretation.

Print Assumptions type_interp_unique.
Print Assumptions reducible_type_candidate.
Print Assumptions type_interp_pi_intro.
Print Assumptions type_interp_sigma_intro.
