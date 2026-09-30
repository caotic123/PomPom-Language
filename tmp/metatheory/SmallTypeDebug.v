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
| sa_enumu : small_atom TEnumU full_SN
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
  intros n R H; destruct H; auto using normalizing_candidate, enum_elements_candidate.
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
      Show.
Abort.
