(* A nested positive atomic model for the complete small type grammar.
   Fixed-point constructors carry candidate certificates. These certificates
   are proved from their description interpretations below; their presence
   keeps atomic validity independent of the recursive coherence proof. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBDescriptionModel.
Import Full.

Definition description_fixed_point RI (F : term -> description_functor) :=
  Indexed.mu RI (fun X i => F i X).

Inductive small_atom : term -> (term -> Prop) -> Prop :=
| sa_unit : small_atom TUnitT full_SN
| sa_uid : small_atom TUId full_SN
| sa_enumu : small_atom TEnumU enumeration_computable
| sa_enum : forall E, small_atom (TEnumT E) (enum_elements E)
| sa_mu : forall IT D i RI F,
    type_interp small_atom IT RI -> RI i ->
    (forall j, RI j -> description_interp small_atom RI (TApp D j) (F j)) ->
    candidate (description_fixed_point RI F i) ->
    small_atom (TApp (TMuI IT D) i) (description_fixed_point RI F i)
| sa_close : forall IT D G i RI FD FG,
    type_interp small_atom IT RI -> RI i ->
    description_interp small_atom RI (TApp D i) FD ->
    (forall j, RI j -> description_interp small_atom RI (TApp G j) (FG j)) ->
    candidate (rolled_elements (FD (description_fixed_point RI FG))) ->
    small_atom (TApp (TClose IT D G) i)
      (rolled_elements (FD (description_fixed_point RI FG))).

Lemma small_atom_candidate : forall n R, small_atom n R -> candidate R.
Proof.
  intros n R H; destruct H; auto using normalizing_candidate, enum_elements_candidate,
    enumeration_computable_candidate.
Qed.
Lemma small_atom_not_neutral : forall n R, small_atom n R -> ~ neutral n.
Proof. intros n R H; destruct H; cbn [neutral]; tauto. Qed.
Lemma small_atom_not_pi : forall A B R, ~ small_atom (TPi A B) R.
Proof. intros A B R H; inversion H. Qed.
Lemma small_atom_not_sigma : forall A B R, ~ small_atom (TSigma A B) R.
Proof. intros A B R H; inversion H. Qed.
Lemma small_atom_not_sort : forall k R, ~ small_atom (TSort k) R.
Proof. intros k R H; inversion H. Qed.

Theorem small_atom_unique : forall n R, small_atom n R ->
  forall S, small_atom n S -> predicate_equiv R S.
Proof.
  fix IH 3. intros n R H; destruct H; intros S HS; inversion HS; subst.
  all: try solve [intro t; tauto].
  - assert (HRI : predicate_equiv RI RI0).
    { eapply type_interp_unique; [exact small_atom_not_neutral|exact small_atom_not_pi
        |exact small_atom_not_sigma|intros n P Q HP HQ; exact (IH n P HP Q HQ)
        |exact H|eassumption|apply cv_refl]. }
    apply Indexed.mu_model_equiv; [exact HRI|].
    intros X HX j Hj.
    eapply description_interp_unique; [exact small_atom_not_neutral|exact small_atom_not_pi
      |exact small_atom_not_sigma|intros n P Q HP HQ; exact (IH n P HP Q HQ)
      |apply H1; exact Hj| |apply cv_refl].
    apply H9, HRI; exact Hj.
  - assert (HRI : predicate_equiv RI RI0).
    { eapply type_interp_unique; [exact small_atom_not_neutral|exact small_atom_not_pi
        |exact small_atom_not_sigma|intros n P Q HP HQ; exact (IH n P HP Q HQ)
        |exact H|eassumption|apply cv_refl]. }
    assert (Hmu : forall j, predicate_equiv (description_fixed_point RI FG j)
      (description_fixed_point RI0 FG0 j)).
    { apply Indexed.mu_model_equiv; [exact HRI|].
      intros X HX j Hj.
      eapply description_interp_unique; [exact small_atom_not_neutral|exact small_atom_not_pi
        |exact small_atom_not_sigma|intros n P Q HP HQ; exact (IH n P HP Q HQ)
        |apply H2; exact Hj| |apply cv_refl].
      apply H12, HRI; exact Hj. }
    assert (HF : functor_equiv FD FD0).
    { eapply description_interp_unique; [exact small_atom_not_neutral|exact small_atom_not_pi
        |exact small_atom_not_sigma|intros n P Q HP HQ; exact (IH n P HP Q HQ)
        |exact H1|eassumption|apply cv_refl]. }
    apply rolled_elements_equiv.
    pose proof (description_interp_family_equiv _ _ _ _ H1 _ _ (fun j _ => Hmu j)) as HE.
    intro t; specialize (HE t); specialize (HF (description_fixed_point RI0 FG0) t); tauto.
Qed.

Lemma small_type_candidate : forall A R, type_interp small_atom A R -> candidate R.
Proof.
  intros A R H; eapply type_interp_candidate;
    [exact small_atom_candidate|exact small_atom_not_neutral|exact small_atom_not_pi
    |exact small_atom_not_sigma|intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)|exact H].
Qed.
Lemma small_description_candidate : forall RI D F,
  description_interp small_atom RI D F -> forall X, Indexed.candidates RI X -> candidate (F X).
Proof.
  intros RI D F H X HX; eapply description_interp_candidate;
    [exact small_atom_not_neutral|exact small_atom_not_pi|exact small_atom_not_sigma
    |intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)|exact small_atom_candidate|exact H|exact HX].
Qed.
Theorem small_fixed_point_candidate : forall RI D F,
  (forall j, RI j -> description_interp small_atom RI (TApp D j) (F j)) ->
  Indexed.candidates RI (description_fixed_point RI F).
Proof.
  intros RI D F HF; apply Indexed.mu_candidate.
  intros i Hi t HT; exact (candidate_normalizing
    (small_description_candidate _ _ _ (HF i Hi) (fun _ => full_SN)
      (fun _ _ => normalizing_candidate)) HT).
Qed.
Theorem small_mu_atom : forall IT D i RI F,
  type_interp small_atom IT RI -> RI i ->
  (forall j, RI j -> description_interp small_atom RI (TApp D j) (F j)) ->
  small_atom (TApp (TMuI IT D) i) (description_fixed_point RI F i).
Proof.
  intros IT D i RI F HI Hi HF; apply sa_mu; try assumption.
  exact (small_fixed_point_candidate RI D F HF i Hi).
Qed.
Theorem small_close_atom : forall IT D G i RI FD FG,
  type_interp small_atom IT RI -> RI i ->
  description_interp small_atom RI (TApp D i) FD ->
  (forall j, RI j -> description_interp small_atom RI (TApp G j) (FG j)) ->
  small_atom (TApp (TClose IT D G) i)
    (rolled_elements (FD (description_fixed_point RI FG))).
Proof.
  intros IT D G i RI FD FG HI Hi HD HG; apply sa_close; try assumption.
  apply rolled_elements_candidate, (small_description_candidate _ _ _ HD).
  exact (small_fixed_point_candidate RI G FG HG).
Qed.

Theorem small_fixed_point_index_equiv : forall RI D F,
  (forall j, RI j -> description_interp small_atom RI (TApp D j) (F j)) ->
  forall i j, RI i -> RI j -> conv i j ->
  predicate_equiv (description_fixed_point RI F i) (description_fixed_point RI F j).
Proof.
  intros RI D F HF i j Hi Hj HC; apply Indexed.mu_index_equiv.
  - intros X Y HXY z Hz t HT; eapply description_interp_monotone; [apply HF; exact Hz|exact HXY|exact HT].
  - intros z Hz t HT; exact (candidate_normalizing
      (small_description_candidate _ _ _ (HF z Hz) (fun _ => full_SN)
        (fun _ _ => normalizing_candidate)) HT).
  - exact Hi.
  - exact Hj.
  - intros X HX; eapply description_interp_unique;
      [exact small_atom_not_neutral|exact small_atom_not_pi|exact small_atom_not_sigma
      |intros n P Q HP HQ; exact (small_atom_unique n P HP Q HQ)
      |apply HF; exact Hi|apply HF; exact Hj|].
    apply cv_compatible, cp_TApp; [apply cv_refl|exact HC].
Qed.

Print Assumptions small_atom_unique.
Print Assumptions small_mu_atom.
Print Assumptions small_close_atom.
