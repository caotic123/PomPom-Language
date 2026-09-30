(* Semantic generation keeps the original codomain guarded by its own
   normalization proof. Substitution need not preserve raw normalization. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBCalculusModel.
Import Full.

Section Generation.
Variable atom : term -> (term -> Prop) -> Prop.
Hypothesis atom_not_pi : forall A B R, ~ atom (TPi A B) R.
Hypothesis atom_not_sigma : forall A B R, ~ atom (TSigma A B) R.

Theorem type_interp_pi_view : forall T R, type_interp atom T R -> forall A B,
  T = TPi A B -> exists RA RB,
  type_interp atom A RA /\ predicate_equiv R (dependent_function RA RB) /\
  (forall a, RA a -> full_SN (subst a 0 B) -> type_interp atom (subst a 0 B) (RB a)).
Proof.
  intros T R H; induction H; intros AA BB HE; subst A.
  - destruct (reduces_binary TPi reduction_pi _ _ _ H0) as [U [V [-> _]]]; contradiction.
  - destruct (reduces_binary TPi reduction_pi _ _ _ H0) as [U [V [-> _]]].
    exfalso; eapply atom_not_pi; eassumption.
  - destruct (reduces_binary TPi reduction_pi _ _ _ H0) as [U' [V' [HE [RU RV]]]].
    inversion HE; subst U' V'; exists RA,RB; split.
    + eapply type_interp_conversion; [exact H2| |apply cv_sym; exact (reductions_conversion _ _ RU)].
      eapply full_SN_map_reflection with (C:=fun a => TPi a BB);
        [intros; now apply red_TPi_A|exact H].
    + split; [intro t; tauto|].
      intros a Ha HS; eapply type_interp_conversion;
        [exact (H3 a Ha)|exact HS|apply cv_sym, reductions_conversion; now apply reductions_subst].
  - destruct (reduces_binary TPi reduction_pi _ _ _ H0) as [U' [V' [HE _]]]; discriminate.
  - destruct (IHtype_interp _ _ eq_refl) as [RA [RB [HA [HR HB]]]].
    exists RA,RB; split; [exact HA|]; split; [intro t; specialize (H0 t); specialize (HR t); tauto|exact HB].
Qed.

Theorem type_interp_sigma_view : forall T R, type_interp atom T R -> forall A B,
  T = TSigma A B -> exists RA RB,
  type_interp atom A RA /\ predicate_equiv R (dependent_pair RA RB) /\
  (forall a, RA a -> full_SN (subst a 0 B) -> type_interp atom (subst a 0 B) (RB a)).
Proof.
  intros T R H; induction H; intros AA BB HE; subst A.
  - destruct (reduces_binary TSigma reduction_sigma _ _ _ H0) as [U [V [-> _]]]; contradiction.
  - destruct (reduces_binary TSigma reduction_sigma _ _ _ H0) as [U [V [-> _]]].
    exfalso; eapply atom_not_sigma; eassumption.
  - destruct (reduces_binary TSigma reduction_sigma _ _ _ H0) as [U' [V' [HE _]]]; discriminate.
  - destruct (reduces_binary TSigma reduction_sigma _ _ _ H0) as [U' [V' [HE [RU RV]]]].
    inversion HE; subst U' V'; exists RA,RB; split.
    + eapply type_interp_conversion; [exact H2| |apply cv_sym; exact (reductions_conversion _ _ RU)].
      eapply full_SN_map_reflection with (C:=fun a => TSigma a BB);
        [intros; now apply red_TSigma_A|exact H].
    + split; [intro t; tauto|].
      intros a Ha HS; eapply type_interp_conversion;
        [exact (H3 a Ha)|exact HS|apply cv_sym, reductions_conversion; now apply reductions_subst].
  - destruct (IHtype_interp _ _ eq_refl) as [RA [RB [HA [HR HB]]]].
    exists RA,RB; split; [exact HA|]; split; [intro t; specialize (H0 t); specialize (HR t); tauto|exact HB].
Qed.

Theorem type_interp_atom_view : forall T R, type_interp atom T R -> forall n,
  normal_form n -> ~ neutral n ->
  (forall A B, n <> TPi A B) -> (forall A B, n <> TSigma A B) ->
  conv T n -> exists S, atom n S /\ predicate_equiv R S.
Proof.
  intros T R H; induction H; intros m HM Hneu Hpi Hsig HC.
  all: try match goal with
    HR : rtc reduction ?T ?n, HN : normal_form ?n |- _ =>
    let HE := fresh "HE" in assert (HE : n = m) by
      (eapply normal_forms_join; [exact HC|exact HR|apply rtc_refl|exact HN|exact HM]);
    subst m
  end.
  - contradiction.
  - exists R; split; [exact H2|intro t; tauto].
  - exfalso; apply (Hpi U V); reflexivity.
  - exfalso; apply (Hsig U V); reflexivity.
  - destruct (IHtype_interp _ HM Hneu Hpi Hsig HC) as [Q [HQ HE]].
    exists Q; split; [exact HQ|intro t; specialize (H0 t); specialize (HE t); tauto].
Qed.
End Generation.

Theorem calculus_sort_view : forall n A R k,
  calculus_interp n A R -> conv A (TSort k) ->
  k < n /\ predicate_equiv R (calculus_type k).
Proof.
  intros n A R k HA HC.
  destruct (type_interp_atom_view _ _ _ HA (TSort k) (sort_normal k)) as [S [HS HE]].
  - cbn [neutral]; tauto.
  - discriminate.
  - discriminate.
  - exact HC.
  - inversion HS; subst.
    + exfalso; eapply primitive_not_sort; eassumption.
    + assert (Hkn : k < n).
      { rewrite <- (universe_levels_length primitive_at n).
        apply nth_error_Some; congruence. }
      pose proof (universe_levels_lookup primitive_at k n Hkn) as HL.
      rewrite H0 in HL.
      inversion HL; subst; auto.
Qed.

Print Assumptions type_interp_pi_view.
Print Assumptions type_interp_sigma_view.
Print Assumptions calculus_sort_view.
