(* Structural universe comparison modulo conversion. The relation is raw;
   its realization theorem needs only formation of its two endpoints. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBCumulativeTyping nameless.DBTypedPiViews.
Import ListNotations.

Inductive type_comparison : term -> term -> Prop :=
| cmp_conversion : forall A B, conv A B -> type_comparison A B
| cmp_sort : forall A B j k,
    conv A (TSort j) -> conv B (TSort k) -> j <= k -> type_comparison A B
| cmp_pi : forall A B U V X Y,
    conv A (TPi U V) -> conv B (TPi X Y) ->
    type_comparison X U -> type_comparison V Y -> type_comparison A B.

Lemma comparison_left_conversion : forall A B,
  type_comparison A B -> forall A', conv A' A -> type_comparison A' B.
Proof. intros A B H; destruct H; intros A' HC;
  [apply cmp_conversion|eapply cmp_sort|eapply cmp_pi]; eauto using cv_trans. Qed.
Lemma comparison_right_conversion : forall A B,
  type_comparison A B -> forall B', conv B B' -> type_comparison A B'.
Proof. intros A B H; destruct H; intros B' HC;
  [apply cmp_conversion|eapply cmp_sort|eapply cmp_pi]; eauto using cv_trans, cv_sym. Qed.

Lemma comparison_universe : forall A B,
  universe_le A B -> type_comparison A B.
Proof. intros A B H; induction H; eauto using type_comparison, cv_refl. Qed.

Lemma comparison_subst : forall A B, type_comparison A B -> forall t c,
  type_comparison (subst t c A) (subst t c B).
Proof.
  intros A B H; induction H; intros t c.
  - apply cmp_conversion; now apply conversion_subst.
  - eapply cmp_sort; [exact (conversion_subst _ _ H t c)|exact (conversion_subst _ _ H0 t c)|exact H1].
  - eapply cmp_pi; [exact (conversion_subst _ _ H t c)|exact (conversion_subst _ _ H0 t c)|auto|auto].
Qed.

Lemma conversion_common_source : forall t A B,
  conv t A -> conv t B -> conv A B.
Proof. intros; eapply cv_trans; [apply cv_sym; eassumption|eassumption]. Qed.
Lemma sort_reductions_identity : forall k t,
  rtc reduction (TSort k) t -> t = TSort k.
Proof.
  intros k t H; remember (TSort k) as s eqn:E; induction H; subst; auto.
  inversion H; discriminate.
Qed.
Lemma conversion_sort_levels : forall j k, conv (TSort j) (TSort k) -> j = k.
Proof.
  intros j k H; destruct (conversion_joinable _ _ H) as [t [Hj Hk]].
  apply sort_reductions_identity in Hj, Hk; congruence.
Qed.
Lemma sort_not_pi_conversion : forall j A B, ~ conv (TSort j) (TPi A B).
Proof. intros j A B H; pose proof (conversion_head _ _ _ _ H eq_refl eq_refl); discriminate. Qed.

Lemma comparison_composition : forall A B, type_comparison A B ->
  (forall C, type_comparison B C -> type_comparison A C) /\
  (forall C, type_comparison C A -> type_comparison C B).
Proof.
  intros A B H; induction H as [A B HAB|A B j k HA HB Hjk|A B U V X Y HA HB HX IHX HY IHY].
  - split; intros C HC; [eapply comparison_left_conversion|eapply comparison_right_conversion]; eassumption.
  - split; intros C HC; destruct HC as [L R HLR|L R l m HL HR Hlm|L R U V X Y HL HR HU HV].
    + eapply comparison_right_conversion; [exact (cmp_sort _ _ _ _ HA HB Hjk)|exact HLR].
    + assert (k = l) by (apply conversion_sort_levels; eapply conversion_common_source; eassumption).
      eapply cmp_sort; [exact HA|exact HR|lia].
    + exfalso; eapply sort_not_pi_conversion; eapply conversion_common_source; [exact HB|exact HL].
    + eapply comparison_left_conversion; [exact (cmp_sort _ _ _ _ HA HB Hjk)|exact HLR].
    + assert (m = j) by (apply conversion_sort_levels; eapply conversion_common_source; eassumption).
      eapply cmp_sort; [exact HL|exact HB|lia].
    + exfalso; eapply sort_not_pi_conversion; eapply conversion_common_source; [exact HA|exact HR].
  - destruct IHX as [HXafter HXbefore], IHY as [HYafter HYbefore].
    split; intros C HC; destruct HC as [L R HLR|L R l m HL HR Hlm|L R U' V' X' Y' HL HR HU HV].
    + eapply comparison_right_conversion; [exact (cmp_pi _ _ _ _ _ _ HA HB HX HY)|exact HLR].
    + exfalso; eapply sort_not_pi_conversion; eapply conversion_common_source; [exact HL|exact HB].
    + destruct (conversion_pi _ _ _ _ (conversion_common_source _ _ _ HB HL)) as [HD HE].
      eapply cmp_pi; [exact HA|exact HR|apply HXbefore|apply HYafter].
      * eapply comparison_right_conversion; [exact HU|now apply cv_sym].
      * eapply comparison_left_conversion; [exact HV|exact HE].
    + eapply comparison_left_conversion; [exact (cmp_pi _ _ _ _ _ _ HA HB HX HY)|exact HLR].
    + exfalso; eapply sort_not_pi_conversion; eapply conversion_common_source; [exact HR|exact HA].
    + destruct (conversion_pi _ _ _ _ (conversion_common_source _ _ _ HA HR)) as [HD HE].
      eapply cmp_pi; [exact HL|exact HB|apply HXafter|apply HYbefore].
      * eapply comparison_left_conversion; [exact HU|exact HD].
      * eapply comparison_right_conversion; [exact HV|now apply cv_sym].
Qed.

Theorem comparison_transitive : forall A B C,
  type_comparison A B -> type_comparison B C -> type_comparison A C.
Proof. intros A B C H; exact (proj1 (comparison_composition _ _ H) C). Qed.

Lemma type_change_comparison : forall Gamma A B,
  type_change Gamma A B -> type_comparison A B.
Proof.
  intros Gamma A B H; induction H;
    eauto using cmp_conversion, comparison_universe, comparison_transitive.
Qed.

Theorem comparison_realization_modulo : forall A B, type_comparison A B ->
  forall Gamma A' B', conv A A' -> conv B B' ->
  type_wf Gamma A' -> type_wf Gamma B' -> type_change Gamma A' B'.
Proof.
  intros A B H; induction H as [A B HC|A B j k HA HB Hjk|A B U V X Y HA HB HX IHX HY IHY];
    intros Gamma AA BB HAA HBB HAf HBf.
  - apply tc_conversion; [exact HAf|exact HBf|].
    eapply cv_trans; [apply cv_sym; exact HAA|eapply cv_trans; [exact HC|exact HBB]].
  - assert (Hctx : wf Gamma) by (destruct HAf as [n Hn]; eauto using typing_context).
    eapply tc_transitive; [apply tc_conversion; [exact HAf|eexists; now apply ty_sort|eapply conversion_common_source; [exact HAA|exact HA]]|].
    eapply tc_transitive with (B:=TSort k); [apply tc_universe; [eexists; now apply ty_sort|eexists; now apply ty_sort|now apply ul_sort]|].
    apply tc_conversion; [eexists; now apply ty_sort|exact HBf|eapply conversion_common_source; [exact HB|exact HBB]].
  - destruct HAf as [j HAf], HBf as [k HBf].
    assert (HAP : conv AA (TPi U V)) by (eapply conversion_common_source; eassumption).
    assert (HBP : conv BB (TPi X Y)) by (eapply conversion_common_source; eassumption).
    destruct (typed_pi_view _ _ _ _ _ HAf HAP) as [U' [V' [HP [HU [HV HC]]]]].
    destruct (typed_pi_view _ _ _ _ _ HBf HBP) as [X' [Y' [HQ [HX' [HY' HD]]]]].
    destruct (pi_components _ _ _ HP _ _ eq_refl) as [ju [jv [HUf HVf]]].
    destruct (pi_components _ _ _ HQ _ _ eq_refl) as [jx [jy [HXf HYf]]].
    assert (HDom : type_change Gamma X' U').
    { apply IHX; [exact HX'|exact HU|eexists; exact HXf|eexists; exact HUf]. }
    assert (HCod : type_change (X'::Gamma) V' Y').
    { apply IHY; [exact HV|exact HY'| |].
      - exists jv; eapply type_change_narrowing; eassumption.
      - exists jy; exact HYf. }
    eapply tc_transitive; [apply tc_conversion; [eexists; exact HAf|eexists; exact HP|exact HC]|].
    eapply tc_transitive; [apply type_change_pi; [exact HDom|exists jv; exact HVf|exact HCod]|].
    apply tc_conversion; [eexists; exact HQ|eexists; exact HBf|now apply cv_sym].
Qed.

Theorem comparison_realization : forall A B, type_comparison A B ->
  forall Gamma, type_wf Gamma A -> type_wf Gamma B -> type_change Gamma A B.
Proof. intros; eapply comparison_realization_modulo; eauto using cv_refl. Qed.

Lemma comparison_pi_inversion : forall A B C D,
  type_comparison (TPi A B) (TPi C D) ->
  type_comparison C A /\ type_comparison B D.
Proof.
  intros A B C D H; inversion H; subst.
  - destruct (conversion_pi _ _ _ _ H0); split; apply cmp_conversion; auto using cv_sym.
  - exfalso; eapply sort_not_pi_conversion; apply cv_sym; eassumption.
  - destruct (conversion_pi _ _ _ _ H0) as [HA HB].
    destruct (conversion_pi _ _ _ _ H1) as [HC HD].
    split.
    + eapply comparison_left_conversion; [eapply comparison_right_conversion; [exact H2|apply cv_sym; exact HA]|exact HC].
    + eapply comparison_left_conversion; [eapply comparison_right_conversion; [exact H3|apply cv_sym; exact HD]|exact HB].
Qed.

Lemma comparison_pi_source : forall A B,
  type_comparison A B -> forall C D, conv B (TPi C D) ->
  exists U V, conv A (TPi U V).
Proof.
  intros A B H; destruct H; intros C D HC.
  - exists C,D; eapply cv_trans; eassumption.
  - exfalso; eapply sort_not_pi_conversion; eapply conversion_common_source; [exact H0|exact HC].
  - eauto.
Qed.

Theorem type_change_strengthening : forall Delta A B c,
  type_change Delta (lift 1 c A) (lift 1 c B) ->
  forall Gamma, type_wf Gamma A -> type_wf Gamma B -> type_change Gamma A B.
Proof.
  intros Delta A B c H Gamma HA HB; apply comparison_realization; try assumption.
  pose proof (comparison_subst _ _ (type_change_comparison _ _ _ H) TUnit c) as HC.
  now rewrite !subst_lift_cancel in HC.
Qed.

Print Assumptions comparison_transitive.
Print Assumptions comparison_realization.
Print Assumptions type_change_strengthening.
