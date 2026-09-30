(* Binder generation retains the normal codomain. Its candidate and stability
   laws hold for every domain element, even when the original codomain needs
   a separate normalization premise after substitution. *)
Require Export nameless.DBCloseIndComputability.
Import Full.

Section NormalBinderViews.
Variable atom : term -> (term -> Prop) -> Prop.
Hypothesis atom_not_pi : forall A B R, ~ atom (TPi A B) R.
Hypothesis atom_not_sigma : forall A B R, ~ atom (TSigma A B) R.

Theorem type_interp_pi_normal_view : forall T R, type_interp atom T R -> forall A B,
  T = TPi A B -> exists RA RB V,
  type_interp atom A RA /\ predicate_equiv R (dependent_function RA RB) /\
  rtc reduction B V /\ (forall a, RA a -> type_interp atom (subst a 0 V) (RB a)).
Proof.
  intros T R H; induction H; intros AA BB HE; subst A.
  - destruct (reduces_binary TPi reduction_pi _ _ _ H0) as [U [V [-> _]]]; contradiction.
  - destruct (reduces_binary TPi reduction_pi _ _ _ H0) as [U [V [-> _]]].
    exfalso; eapply atom_not_pi; eassumption.
  - destruct (reduces_binary TPi reduction_pi _ _ _ H0) as [U' [V' [HE [RU RV]]]].
    inversion HE; subst U' V'; exists RA,RB,V; split.
    + eapply type_interp_conversion; [exact H2| |apply cv_sym; exact (reductions_conversion _ _ RU)].
      eapply full_SN_map_reflection with (C:=fun a => TPi a BB);
        [intros; now apply red_TPi_A|exact H].
    + split; [intro t; tauto|]; auto.
  - destruct (reduces_binary TPi reduction_pi _ _ _ H0) as [U' [V' [HE _]]]; discriminate.
  - destruct (IHtype_interp _ _ eq_refl) as (RA & RB & V & HA & HR & HV & HB).
    exists RA,RB,V; split; [exact HA|]; split; [|auto].
    intro t; specialize (H0 t); specialize (HR t); tauto.
Qed.
Theorem type_interp_sigma_normal_view : forall T R, type_interp atom T R -> forall A B,
  T = TSigma A B -> exists RA RB V,
  type_interp atom A RA /\ predicate_equiv R (dependent_pair RA RB) /\
  rtc reduction B V /\ (forall a, RA a -> type_interp atom (subst a 0 V) (RB a)).
Proof.
  intros T R H; induction H; intros AA BB HE; subst A.
  - destruct (reduces_binary TSigma reduction_sigma _ _ _ H0) as [U [V [-> _]]]; contradiction.
  - destruct (reduces_binary TSigma reduction_sigma _ _ _ H0) as [U [V [-> _]]].
    exfalso; eapply atom_not_sigma; eassumption.
  - destruct (reduces_binary TSigma reduction_sigma _ _ _ H0) as [U' [V' [HE _]]]; discriminate.
  - destruct (reduces_binary TSigma reduction_sigma _ _ _ H0) as [U' [V' [HE [RU RV]]]].
    inversion HE; subst U' V'; exists RA,RB,V; split.
    + eapply type_interp_conversion; [exact H2| |apply cv_sym; exact (reductions_conversion _ _ RU)].
      eapply full_SN_map_reflection with (C:=fun a => TSigma a BB);
        [intros; now apply red_TSigma_A|exact H].
    + split; [intro t; tauto|]; auto.
  - destruct (IHtype_interp _ _ eq_refl) as (RA & RB & V & HA & HR & HV & HB).
    exists RA,RB,V; split; [exact HA|]; split; [|auto].
    intro t; specialize (H0 t); specialize (HR t); tauto.
Qed.
End NormalBinderViews.

Lemma calculus_codomain_stable : forall n A B RB,
  candidate A -> (forall a, A a -> calculus_interp n (subst a 0 B) (RB a)) -> stable_family A RB.
Proof.
  intros n A B RB CA HB a a' Ha HR.
  eapply calculus_interp_unique; [exact (HB a Ha)|exact (HB a' (candidate_reduct CA Ha HR))|].
  apply reductions_conversion; now apply reduction_subst_argument.
Qed.
Lemma calculus_pi_components : forall n A B R, calculus_interp n (TPi A B) R ->
  exists RA RB, calculus_interp n A RA /\ predicate_equiv R (dependent_function RA RB) /\
  (forall a, RA a -> candidate (RB a)) /\ stable_family RA RB /\
  (forall a, RA a -> full_SN (subst a 0 B) -> calculus_interp n (subst a 0 B) (RB a)).
Proof.
  intros n A B R HT.
  destruct (type_interp_pi_normal_view _ ltac:(apply level_atom_not_pi; exact primitive_not_pi) _ _ HT A B eq_refl) as (RA & RB & V & HA & HE & HV & HB).
  exists RA,RB; split; [exact HA|]; split; [exact HE|]; split.
  - intros a Ha; exact (calculus_interp_candidate n _ _ (HB a Ha)).
  - split; [eapply calculus_codomain_stable; [exact (calculus_interp_candidate _ _ _ HA)|exact HB]|].
      intros a Ha HS; eapply type_interp_conversion; [exact (HB a Ha)|exact HS|].
      apply cv_sym, reductions_conversion; now apply reductions_subst.
Qed.
Lemma calculus_sigma_components : forall n A B R, calculus_interp n (TSigma A B) R ->
  exists RA RB, calculus_interp n A RA /\ predicate_equiv R (dependent_pair RA RB) /\
  (forall a, RA a -> candidate (RB a)) /\ stable_family RA RB /\
  (forall a, RA a -> full_SN (subst a 0 B) -> calculus_interp n (subst a 0 B) (RB a)).
Proof.
  intros n A B R HT.
  destruct (type_interp_sigma_normal_view _ ltac:(apply level_atom_not_sigma; exact primitive_not_sigma) _ _ HT A B eq_refl) as (RA & RB & V & HA & HE & HV & HB).
  exists RA,RB; split; [exact HA|]; split; [exact HE|]; split.
  - intros a Ha; exact (calculus_interp_candidate n _ _ (HB a Ha)).
  - split; [eapply calculus_codomain_stable; [exact (calculus_interp_candidate _ _ _ HA)|exact HB]|].
      intros a Ha HS; eapply type_interp_conversion; [exact (HB a Ha)|exact HS|].
      apply cv_sym, reductions_conversion; now apply reductions_subst.
Qed.

Print Assumptions calculus_pi_components.
Print Assumptions calculus_sigma_components.
