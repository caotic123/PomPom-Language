(* Positive semantic functors for descriptions, separately from the strong
   computability of their original function fields. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBEnumCandidates.
Import Full.

Definition payload_family := term -> term -> Prop.
Definition description_functor := payload_family -> term -> Prop.
Definition functor_equiv (F G : description_functor) :=
  forall X, predicate_equiv (F X) (G X).

Section DescriptionInterpretation.
Variable atom : term -> (term -> Prop) -> Prop.

Inductive description_interp (RI : term -> Prop) : term -> description_functor -> Prop :=
| di_neutral : forall D n,
    full_SN D -> rtc reduction D n -> normal_form n -> neutral n ->
    description_interp RI D (fun _ => full_SN)
| di_var : forall D i,
    full_SN D -> rtc reduction D (TIVar i) -> normal_form (TIVar i) -> RI i ->
    description_interp RI D (fun X => X i)
| di_one : forall D,
    full_SN D -> rtc reduction D TI1 ->
    description_interp RI D (fun _ => full_SN)
| di_bot : forall D,
    full_SN D -> rtc reduction D TIBot ->
    description_interp RI D (fun _ => empty_elements)
| di_prod : forall D A B FA FB,
    full_SN D -> rtc reduction D (TIProd A B) -> normal_form (TIProd A B) ->
    description_interp RI A FA -> description_interp RI B FB ->
    description_interp RI D (fun X => dependent_pair (FA X) (fun _ => FB X))
| di_pi : forall D A f RA F,
    full_SN D -> rtc reduction D (TIPi A f) -> normal_form (TIPi A f) ->
    type_interp atom A RA ->
    (forall a, RA a -> description_interp RI (TApp f a) (F a)) ->
    description_interp RI D (fun X => dependent_function RA (fun a => F a X))
| di_sigma : forall D A f RA F,
    full_SN D -> rtc reduction D (TISig A f) -> normal_form (TISig A f) ->
    type_interp atom A RA ->
    (forall a, RA a -> description_interp RI (TApp f a) (F a)) ->
    description_interp RI D (fun X => dependent_pair RA (fun a => F a X))
| di_choice : forall D E f RE F,
    full_SN D -> rtc reduction D (TIChoice E f) -> normal_form (TIChoice E f) ->
    type_interp atom (TEnumT E) RE ->
    (forall e, RE e -> description_interp RI (TApp f e) (F e)) ->
    description_interp RI D (fun X => dependent_pair RE (fun e => F e X))
| di_equiv : forall D F G,
    description_interp RI D F -> functor_equiv F G ->
    description_interp RI D G.

Lemma description_interp_normalizing : forall RI D F,
  description_interp RI D F -> full_SN D.
Proof. intros RI D F H; induction H; assumption. Qed.
Lemma one_description_normal : normal_form TI1.
Proof. intros u H; inversion H; discriminate. Qed.
Lemma bot_description_normal : normal_form TIBot.
Proof. intros u H; inversion H; discriminate. Qed.
Lemma description_interp_conversion : forall RI D F, description_interp RI D F ->
  forall E, full_SN E -> conv D E -> description_interp RI E F.
Proof.
  intros RI D F H; induction H; intros Z HE HC.
  all: try solve [eapply di_neutral; [exact HE|eapply conversion_to_normal; eassumption|eassumption|eassumption]].
  all: try solve [eapply di_var; [exact HE|eapply conversion_to_normal; eassumption|eassumption|eassumption]].
  - eapply di_one; [exact HE|eapply conversion_to_normal; eauto using one_description_normal].
  - eapply di_bot; [exact HE|eapply conversion_to_normal; eauto using bot_description_normal].
  - eapply di_prod; [exact HE|eapply conversion_to_normal; eassumption|eassumption|eassumption|eassumption].
  - eapply di_pi; [exact HE|eapply conversion_to_normal; eassumption|eassumption|eassumption|eassumption].
  - eapply di_sigma; [exact HE|eapply conversion_to_normal; eassumption|eassumption|eassumption|eassumption].
  - eapply di_choice; [exact HE|eapply conversion_to_normal; eassumption|eassumption|eassumption|eassumption].
  - eapply di_equiv; [eapply IHdescription_interp; eassumption|eassumption].
Qed.
Lemma description_interp_reductions : forall RI D F, description_interp RI D F ->
  forall E, rtc reduction D E -> description_interp RI E F.
Proof.
  intros RI D F H E HR; eapply description_interp_conversion;
    [exact H|eapply full_SN_reductions; [eapply description_interp_normalizing; exact H|exact HR]
    |exact (reductions_conversion _ _ HR)].
Qed.

Hypothesis atom_not_neutral : forall n R, atom n R -> ~ neutral n.
Hypothesis atom_not_pi : forall A B R, ~ atom (TPi A B) R.
Hypothesis atom_not_sigma : forall A B R, ~ atom (TSigma A B) R.
Hypothesis atom_unique : forall n R S, atom n R -> atom n S -> predicate_equiv R S.

Lemma description_domain_unique : forall A R S,
  type_interp atom A R -> type_interp atom A S -> predicate_equiv R S.
Proof. intros; eapply type_interp_unique; eauto using cv_refl. Defined.

Theorem description_interp_unique : forall RI D F, description_interp RI D F ->
  forall RI' E G, description_interp RI' E G -> conv D E -> functor_equiv F G.
Proof.
  intros RI D F HA; induction HA; intros RI' EE GG HB HC.
  all: try solve [intros X t; specialize (IHHA _ _ _ HB HC X t); specialize (H X t); tauto].
  all: induction HB.
  all: try solve [match goal with
    IH : conv ?A ?B -> functor_equiv ?F ?G,
    HE : functor_equiv ?G ?G', HC : conv ?A ?B |- functor_equiv ?F ?G' =>
    intros X t; pose proof (IH HC X t); pose proof (HE X t); tauto end].
  all: try (let HN := fresh "HN" in
    pose proof one_description_normal as HN;
    let HM := fresh "HM" in pose proof bot_description_normal as HM).
  all: try match goal with
    HL : rtc reduction ?A ?n, HNL : normal_form ?n,
    HR : rtc reduction ?B ?m, HNR : normal_form ?m,
    HC : conv ?A ?B |- _ =>
    let HE := fresh "HE" in
    assert (HE : n = m) by (eapply normal_forms_join; eassumption);
    first [is_var m; subst m
      |lazymatch n with TIVar _ => lazymatch m with TIVar _ => injection HE as <- end end
      |lazymatch n with TIProd _ _ => lazymatch m with TIProd _ _ => injection HE as <- <- end end
      |lazymatch n with TIPi _ _ => lazymatch m with TIPi _ _ => injection HE as <- <- end end
      |lazymatch n with TISig _ _ => lazymatch m with TISig _ _ => injection HE as <- <- end end
      |lazymatch n with TIChoice _ _ => lazymatch m with TIChoice _ _ => injection HE as <- <- end end
      |inversion HE; subst]; try clear HE
  end.
  all: try solve [cbn [neutral] in *; contradiction].
  all: try solve [intros X t; tauto].
  - intro X; apply dependent_pair_equiv.
    + exact (IHHA1 _ _ _ HB1 (cv_refl _) X).
    + intros a Ha; exact (IHHA2 _ _ _ HB2 (cv_refl _) X).
  - intro X; apply dependent_function_equiv.
    + eapply description_domain_unique; eassumption.
    + intros a Ha; refine (H4 a Ha _ _ _ (H9 a _) (cv_refl _) X).
      exact (proj1 (description_domain_unique _ _ _ H2 H8 a) Ha).
  - intro X; apply dependent_pair_equiv.
    + eapply description_domain_unique; eassumption.
    + intros a Ha; refine (H4 a Ha _ _ _ (H9 a _) (cv_refl _) X).
      exact (proj1 (description_domain_unique _ _ _ H2 H8 a) Ha).
  - intro X; apply dependent_pair_equiv.
    + eapply description_domain_unique; eassumption.
    + intros a Ha; refine (H4 a Ha _ _ _ (H9 a _) (cv_refl _) X).
      exact (proj1 (description_domain_unique _ _ _ H2 H8 a) Ha).
Defined.

Hypothesis atom_candidate : forall n R, atom n R -> candidate R.

Lemma description_domain_candidate : forall A R, type_interp atom A R -> candidate R.
Proof. intros; eapply type_interp_candidate; eassumption. Qed.

Theorem description_interp_candidate : forall RI D F,
  description_interp RI D F -> forall X, Indexed.candidates RI X -> candidate (F X).
Proof.
  intros RI D F H; induction H; intros X HX.
  - exact normalizing_candidate.
  - apply HX; assumption.
  - exact normalizing_candidate.
  - exact empty_elements_candidate.
  - apply dependent_pair_candidate; [now apply IHdescription_interp1|intros; now apply IHdescription_interp2|].
    intros a a' Ha HR t; tauto.
  - apply dependent_function_candidate.
    + eapply description_domain_candidate; eassumption.
    + intros a Ha; now apply H4.
    + intros a a' Ha HR.
      assert (Ha' : RA a') by (eapply candidate_reduct; [eapply description_domain_candidate; exact H2|exact Ha|exact HR]).
      eapply description_interp_unique; [apply H3; exact Ha|apply H3; exact Ha'|].
      apply reductions_conversion, rtc_one; now apply red_TApp_a.
  - apply dependent_pair_candidate.
    + eapply description_domain_candidate; eassumption.
    + intros a Ha; now apply H4.
    + intros a a' Ha HR.
      assert (Ha' : RA a') by (eapply candidate_reduct; [eapply description_domain_candidate; exact H2|exact Ha|exact HR]).
      eapply description_interp_unique; [apply H3; exact Ha|apply H3; exact Ha'|].
      apply reductions_conversion, rtc_one; now apply red_TApp_a.
  - apply dependent_pair_candidate.
    + eapply description_domain_candidate; eassumption.
    + intros a Ha; now apply H4.
    + intros a a' Ha HR.
      assert (Ha' : RE a') by (eapply candidate_reduct; [eapply description_domain_candidate; exact H2|exact Ha|exact HR]).
      eapply description_interp_unique; [apply H3; exact Ha|apply H3; exact Ha'|].
      apply reductions_conversion, rtc_one; now apply red_TApp_a.
  - exact (candidate_equiv _ _ (IHdescription_interp X HX) (H0 X)).
Qed.

Definition description_elements RI D X t :=
  forall F, description_interp RI D F -> F X t.
Lemma description_elements_equiv : forall RI D F, description_interp RI D F ->
  functor_equiv F (description_elements RI D).
Proof.
  intros RI D F HF X t; split.
  - intros H G HG; apply (description_interp_unique _ _ _ HF _ _ _ HG (cv_refl _) X t); exact H.
  - intro H; exact (H F HF).
Qed.
Theorem description_interp_canonical : forall RI D,
  (exists F, description_interp RI D F) -> description_interp RI D (description_elements RI D).
Proof. intros RI D [F HF]; eapply di_equiv; [exact HF|now apply description_elements_equiv]. Qed.

Theorem description_interp_prod_intro : forall RI A B FA FB,
  description_interp RI A FA -> description_interp RI B FB ->
  description_interp RI (TIProd A B) (fun X => dependent_pair (FA X) (fun _ => FB X)).
Proof.
  intros RI A B FA FB HA HB.
  pose proof (description_interp_normalizing _ _ _ HA) as HSA.
  pose proof (description_interp_normalizing _ _ _ HB) as HSB.
  destruct (normalize_full _ HSA) as [A' [RA NA]].
  destruct (normalize_full _ HSB) as [B' [RB NB]].
  eapply di_prod with (A:=A') (B:=B').
  - now apply full_SN_iprod.
  - now apply red_star_TIProd.
  - apply normal_form_binary; [description_components|exact NA|exact NB].
  - eapply description_interp_reductions; eassumption.
  - eapply description_interp_reductions; eassumption.
Qed.

Theorem description_interp_pi_intro : forall RI A f RA F,
  type_interp atom A RA -> full_SN f ->
  (forall a, RA a -> description_interp RI (TApp f a) (F a)) ->
  description_interp RI (TIPi A f) (fun X => dependent_function RA (fun a => F a X)).
Proof.
  intros RI A f RA F HA Hf HF.
  pose proof (type_interp_normalizing _ _ _ HA) as HSA.
  destruct (normalize_full _ HSA) as [A' [RA' NA]].
  destruct (normalize_full _ Hf) as [f' [Rf Nf]].
  eapply di_pi with (A:=A') (f:=f').
  - now apply full_SN_ipi.
  - now apply red_star_TIPi.
  - apply normal_form_binary; [description_components|exact NA|exact Nf].
  - eapply type_interp_reductions; eassumption.
  - intros a Ha; eapply description_interp_reductions; [exact (HF a Ha)|].
    apply red_star_TApp; [exact Rf|constructor].
Qed.
Theorem description_interp_sigma_intro : forall RI A f RA F,
  type_interp atom A RA -> full_SN f ->
  (forall a, RA a -> description_interp RI (TApp f a) (F a)) ->
  description_interp RI (TISig A f) (fun X => dependent_pair RA (fun a => F a X)).
Proof.
  intros RI A f RA F HA Hf HF.
  pose proof (type_interp_normalizing _ _ _ HA) as HSA.
  destruct (normalize_full _ HSA) as [A' [RA' NA]].
  destruct (normalize_full _ Hf) as [f' [Rf Nf]].
  eapply di_sigma with (A:=A') (f:=f').
  - now apply full_SN_isig.
  - now apply red_star_TISig.
  - apply normal_form_binary; [description_components|exact NA|exact Nf].
  - eapply type_interp_reductions; eassumption.
  - intros a Ha; eapply description_interp_reductions; [exact (HF a Ha)|].
    apply red_star_TApp; [exact Rf|constructor].
Qed.
Theorem description_interp_choice_intro : forall RI E f RE F,
  type_interp atom (TEnumT E) RE -> full_SN f ->
  (forall a, RE a -> description_interp RI (TApp f a) (F a)) ->
  description_interp RI (TIChoice E f) (fun X => dependent_pair RE (fun a => F a X)).
Proof.
  intros RI E f RE F HE Hf HF.
  pose proof (full_SN_enumt_reflection _ (type_interp_normalizing _ _ _ HE)) as HSE.
  destruct (normalize_full _ HSE) as [E' [RE' NE]].
  destruct (normalize_full _ Hf) as [f' [Rf Nf]].
  eapply di_choice with (E:=E') (f:=f').
  - now apply full_SN_ichoice.
  - now apply red_star_TIChoice.
  - apply normal_form_binary; [description_components|exact NE|exact Nf].
  - eapply type_interp_reductions; [exact HE|now apply red_star_TEnumT].
  - intros a Ha; eapply description_interp_reductions; [exact (HF a Ha)|].
    apply red_star_TApp; [exact Rf|constructor].
Qed.
End DescriptionInterpretation.

Theorem description_interp_monotone : forall atom RI D F,
  description_interp atom RI D F -> forall X Y,
  Indexed.inclusion RI X Y -> forall t, F X t -> F Y t.
Proof.
  intros atom RI D F H; induction H; intros X Y HI t HT; try exact HT.
  - now apply HI.
  - destruct HT as [HS [HA HB]]; split; [exact HS|]; split;
      [eapply IHdescription_interp1|eapply IHdescription_interp2]; eassumption.
  - destruct HT as [HS HF]; split; [exact HS|]; intros a Ha; eapply H4; eauto.
  - destruct HT as [HS [HA HB]]; split; [exact HS|]; split; [exact HA|]; eapply H4; eauto.
  - destruct HT as [HS [HA HB]]; split; [exact HS|]; split; [exact HA|]; eapply H4; eauto.
  - apply (H0 Y t), (IHdescription_interp X Y HI t), (H0 X t); exact HT.
Qed.

Theorem description_interp_index_inclusion : forall atom RI D F,
  description_interp atom RI D F -> forall RI',
  (forall i, RI i -> RI' i) -> description_interp atom RI' D F.
Proof.
  intros atom RI D F H; induction H; intros RI' HI;
    solve [eapply di_neutral; eassumption|eapply di_var; [eassumption|eassumption|eassumption|now apply HI]
      |eapply di_one; eassumption|eapply di_bot; eassumption|eapply di_prod; eauto
      |eapply di_pi; eauto|eapply di_sigma; eauto|eapply di_choice; eauto|eapply di_equiv; eauto].
Qed.

Theorem description_interp_family_equiv : forall atom RI D F,
  description_interp atom RI D F -> forall X Y,
  (forall i, RI i -> predicate_equiv (X i) (Y i)) -> predicate_equiv (F X) (F Y).
Proof.
  intros atom RI D F HF X Y HE t; split; apply (description_interp_monotone _ _ _ _ HF);
    intros i Hi u Hu; apply (HE i Hi u); exact Hu.
Qed.

Section DescriptionMeaningExistence.
Variable atom : term -> (term -> Prop) -> Prop.
Hypothesis atom_not_neutral : forall n R, atom n R -> ~ neutral n.
Hypothesis atom_not_pi : forall A B R, ~ atom (TPi A B) R.
Hypothesis atom_not_sigma : forall A B R, ~ atom (TSigma A B) R.
Hypothesis atom_unique : forall n R S, atom n R -> atom n S -> predicate_equiv R S.
Variable RI : term -> Prop.
Hypothesis index_candidate : candidate RI.

Theorem computable_description_interpreted : forall D,
  description_computable atom RI D -> exists F, description_interp atom RI D F.
Proof.
  intros D H; induction H.
  - destruct (normalize_full _ H0) as [i' [HR HN]].
    exists (fun X => X i'); eapply di_var.
    + now apply full_SN_ivar.
    + now apply red_star_TIVar.
    + intros u HU; inversion HU; subst; [discriminate|eapply HN; eassumption].
    + eapply candidate_reducts; eassumption.
  - exists (fun _ => full_SN); apply di_one;
      [apply normal_form_accessible, one_description_normal|constructor].
  - exists (fun _ => empty_elements); apply di_bot;
      [apply normal_form_accessible, bot_description_normal|constructor].
  - destruct IHdescription_computable1 as [FA HA]; destruct IHdescription_computable2 as [FB HB].
    eexists; eapply description_interp_prod_intro; eassumption.
  - eexists; eapply description_interp_pi_intro; [exact H|exact H0|].
    intros a Ha; eapply description_interp_canonical; [exact atom_not_neutral|exact atom_not_pi
      |exact atom_not_sigma|exact atom_unique|now apply H2].
  - eexists; eapply description_interp_sigma_intro; [exact H|exact H0|].
    intros a Ha; eapply description_interp_canonical; [exact atom_not_neutral|exact atom_not_pi
      |exact atom_not_sigma|exact atom_unique|now apply H2].
  - eexists; eapply description_interp_choice_intro; [exact H|exact H0|].
    intros a Ha; eapply description_interp_canonical; [exact atom_not_neutral|exact atom_not_pi
      |exact atom_not_sigma|exact atom_unique|now apply H2].
  - destruct IHdescription_computable as [F HF]; exists F.
    eapply description_interp_reductions; [exact HF|now apply rtc_one].
  - assert (HS : full_SN D).
    { constructor; intros E HE; destruct (H1 E HE) as [F HF].
      exact (description_interp_normalizing _ _ _ _ HF). }
    destruct (full_next D) as [E|] eqn:HN.
    + pose proof (full_next_sound _ _ HN) as HR.
      destruct (H1 E HR) as [F HF]; exists F.
      eapply description_interp_conversion; [exact HF|exact HS|].
      apply cv_sym, reductions_conversion, rtc_one; exact HR.
    + exists (fun _ => full_SN); eapply di_neutral with (n:=D).
      * exact HS.
      * apply rtc_refl.
      * exact (full_next_complete _ HN).
      * exact H.
Qed.
End DescriptionMeaningExistence.

Print Assumptions description_interp_unique.
Print Assumptions description_interp_candidate.
Print Assumptions description_interp_canonical.
Print Assumptions description_interp_monotone.
Print Assumptions computable_description_interpreted.
