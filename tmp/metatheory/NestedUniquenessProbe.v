Require Import nameless.DBDescriptionModel.
Import Full.
Section Local.
Variable atom : term -> (term -> Prop) -> Prop.
Hypothesis atom_not_neutral : forall n R, atom n R -> ~ neutral n.
Hypothesis atom_not_pi : forall A B R, ~ atom (TPi A B) R.
Hypothesis atom_not_sigma : forall A B R, ~ atom (TSigma A B) R.
Hypothesis atom_unique : forall n R S, atom n R -> atom n S -> predicate_equiv R S.
Lemma type_interp_unique_transparent : forall A R, type_interp atom A R ->
  forall B S, type_interp atom B S -> conv A B -> predicate_equiv R S.
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
    first [is_var m; subst m
      |lazymatch n with TPi _ _ => lazymatch m with TPi _ _ => injection HE as <- <- end end
      |lazymatch n with TSigma _ _ => lazymatch m with TSigma _ _ => injection HE as <- <- end end
      |inversion HE; subst]; try clear HE
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
Defined.
End Local.
Inductive toy : term -> (term -> Prop) -> Prop :=
| toy_unit : toy TUnitT full_SN
| toy_box : forall A R, type_interp toy A R -> toy (TEnumT A) R.
Lemma toy_not_neutral : forall A R, toy A R -> ~ neutral A.
Proof. intros A R H; destruct H; cbn [neutral]; tauto. Qed.
Lemma toy_not_pi : forall A B R, ~ toy (TPi A B) R.
Proof. intros A B R H; inversion H. Qed.
Lemma toy_not_sigma : forall A B R, ~ toy (TSigma A B) R.
Proof. intros A B R H; inversion H. Qed.
Lemma toy_unique : forall A R, toy A R -> forall S, toy A S -> predicate_equiv R S.
Proof.
  fix IH 3. intros A R H; destruct H; intros S HS; inversion HS; subst.
  - intro t; tauto.
  - eapply type_interp_unique_transparent; [exact toy_not_neutral|exact toy_not_pi|exact toy_not_sigma
      |intros n P Q HP HQ; exact (IH n P HP Q HQ)|eassumption|eassumption|apply cv_refl].
Defined.
Print Assumptions toy_unique.
