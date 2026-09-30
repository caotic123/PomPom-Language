(* Computability of description values controls their original function
   fields at every computable argument, including before normalization. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBUniverseModel nameless.DBIndexedCandidates.
Import Full.

Lemma full_SN_unary : forall C : term -> term,
  (forall a u, reduction (C a) u ->
    exists a', reduction a a' /\ u = C a') ->
  forall a, full_SN a -> full_SN (C a).
Proof.
  intros C HC a H; induction H as [a H IH]; constructor; intros u HU.
  destruct (HC a u HU) as [a' [HR ->]]; now apply IH.
Qed.

Ltac description_components :=
  intros; match goal with H : reduction _ _ |- _ => inversion H; subst end;
  try discriminate; eauto.

Lemma full_SN_ivar : forall i, full_SN i -> full_SN (TIVar i).
Proof. apply full_SN_unary; description_components. Qed.
Lemma full_SN_iprod : forall A B, full_SN A -> full_SN B -> full_SN (TIProd A B).
Proof. apply full_SN_binary; description_components. Qed.
Lemma full_SN_ipi : forall A D, full_SN A -> full_SN D -> full_SN (TIPi A D).
Proof. apply full_SN_binary; description_components. Qed.
Lemma full_SN_isig : forall A D, full_SN A -> full_SN D -> full_SN (TISig A D).
Proof. apply full_SN_binary; description_components. Qed.
Lemma full_SN_ichoice : forall E D, full_SN E -> full_SN D -> full_SN (TIChoice E D).
Proof. apply full_SN_binary; description_components. Qed.
Lemma full_SN_enumt_reflection : forall E, full_SN (TEnumT E) -> full_SN E.
Proof. apply full_SN_map_reflection; intros; now apply red_TEnumT_E. Qed.

Section DescriptionComputability.
Variable atom : term -> (term -> Prop) -> Prop.
Variable RI : term -> Prop.

Inductive description_computable : term -> Prop :=
| dc_var : forall i, RI i -> full_SN i -> description_computable (TIVar i)
| dc_one : description_computable TI1
| dc_bot : description_computable TIBot
| dc_prod : forall A B,
    description_computable A -> description_computable B ->
    description_computable (TIProd A B)
| dc_pi : forall A D RA,
    type_interp atom A RA -> full_SN D ->
    (forall a, RA a -> description_computable (TApp D a)) ->
    description_computable (TIPi A D)
| dc_sigma : forall A D RA,
    type_interp atom A RA -> full_SN D ->
    (forall a, RA a -> description_computable (TApp D a)) ->
    description_computable (TISig A D)
| dc_choice : forall E D RE,
    type_interp atom (TEnumT E) RE -> full_SN D ->
    (forall e, RE e -> description_computable (TApp D e)) ->
    description_computable (TIChoice E D)
| dc_reduct : forall D D',
    description_computable D -> reduction D D' -> description_computable D'
| dc_neutral : forall D,
    neutral D -> (forall D', reduction D D' -> description_computable D') ->
    description_computable D.

Theorem description_computable_normalizing : forall D,
  description_computable D -> full_SN D.
Proof.
  intros D H; induction H.
  - now apply full_SN_ivar.
  - apply normal_form_accessible; intros u HU; inversion HU; discriminate.
  - apply normal_form_accessible; intros u HU; inversion HU; discriminate.
  - now apply full_SN_iprod.
  - apply full_SN_ipi; [eapply type_interp_normalizing; eassumption|assumption].
  - apply full_SN_isig; [eapply type_interp_normalizing; eassumption|assumption].
  - apply full_SN_ichoice; [apply full_SN_enumt_reflection;
      eapply type_interp_normalizing; eassumption|assumption].
  - exact (Acc_inv IHdescription_computable H0).
  - constructor; exact H1.
Qed.
Theorem description_computable_candidate : candidate description_computable.
Proof.
  constructor; [exact description_computable_normalizing|exact dc_reduct|exact dc_neutral].
Qed.
Lemma description_function : forall A D RA,
  type_interp atom A RA -> dependent_function RA (fun _ => description_computable) D ->
  description_computable (TIPi A D) /\ description_computable (TISig A D).
Proof. intros A D RA HA [HD HF]; split; [eapply dc_pi|eapply dc_sigma]; eassumption. Qed.
End DescriptionComputability.

Theorem description_computable_monotone : forall atom atom' RI RI',
  (forall A R, atom A R -> atom' A R) ->
  (forall i, RI i -> RI' i) -> forall D,
  description_computable atom RI D -> description_computable atom' RI' D.
Proof.
  intros atom atom' RI RI' HA HI D H; induction H.
  - apply dc_var; [now apply HI|assumption].
  - apply dc_one.
  - apply dc_bot.
  - now apply dc_prod.
  - eapply dc_pi; [eapply type_interp_monotone; eassumption|assumption|assumption].
  - eapply dc_sigma; [eapply type_interp_monotone; eassumption|assumption|assumption].
  - eapply dc_choice; [eapply type_interp_monotone; eassumption|assumption|assumption].
  - eapply dc_reduct; eassumption.
  - now apply dc_neutral.
Qed.
Corollary description_computable_equiv : forall atom RI RI',
  predicate_equiv RI RI' ->
  predicate_equiv (description_computable atom RI) (description_computable atom RI').
Proof.
  intros atom RI RI' HE D; split; apply description_computable_monotone;
    [auto|intros i Hi; now apply HE|auto|intros i Hi; now apply HE].
Qed.

Print Assumptions description_computable_candidate.
Print Assumptions description_computable_equiv.
