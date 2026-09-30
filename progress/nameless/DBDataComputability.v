(* Computable definitions and the semantic fold/unfold law. These do not
   introduce a judgmental unfolding equation for close types. *)
Require Export nameless.DBIndComputability.
Import Full.

Definition computable_definition RI D := full_SN D /\
  forall i, RI i -> small_code RI (TApp D i).
Definition definition_meaning RI D i := code_meaning RI (TApp D i).
Lemma computable_definition_meaning : forall RI, candidate RI -> forall D,
  computable_definition RI D -> forall i, RI i ->
  small_description RI (TApp D i) (definition_meaning RI D i).
Proof. intros RI CRI D HD i Hi; apply small_code_meaning; [exact CRI|exact (proj2 HD i Hi)]. Qed.
Lemma computable_definition_reductions : forall RI D,
  computable_definition RI D -> forall D', rtc reduction D D' -> computable_definition RI D'.
Proof.
  intros RI D [HS HD] D' HR; split; [exact (full_SN_reductions _ HS _ HR)|].
  intros i Hi; eapply candidate_reducts; [apply description_computable_candidate| |exact (HD i Hi)].
  apply red_star_TApp; [exact HR|constructor].
Qed.
Lemma definition_meaning_conversion : forall RI, candidate RI -> forall D E i j,
  computable_definition RI D -> computable_definition RI E -> RI i -> RI j ->
  conv D E -> conv i j -> functor_equiv (definition_meaning RI D i) (definition_meaning RI E j).
Proof.
  intros RI CRI D E i j HD HE Hi Hj HC HI; eapply small_description_unique;
    [exact (computable_definition_meaning RI CRI D HD i Hi)
    |exact (computable_definition_meaning RI CRI E HE j Hj)|].
  apply cv_compatible, cp_TApp; assumption.
Qed.
Theorem small_fixed_point_rolled_equiv : forall RI D F,
  (forall i, RI i -> small_description RI (TApp D i) (F i)) -> forall i, RI i ->
  predicate_equiv (description_fixed_point RI F i)
    (rolled_elements (F i (description_fixed_point RI F))).
Proof.
  intros RI D F HD i Hi.
  assert (HM : forall X Y, Indexed.inclusion RI X Y ->
    Indexed.inclusion RI (fun i => F i X) (fun i => F i Y)).
  { intros X Y HXY j Hj t Ht; eapply description_interp_monotone;
      [exact (HD j Hj)|exact HXY|exact Ht]. }
  assert (HN : forall j, RI j -> forall t, F j (fun _ => full_SN) t -> full_SN t).
  { intros j Hj t Ht; exact (candidate_normalizing
      (small_description_candidate _ _ _ (HD j Hj) _ (fun _ _ => normalizing_candidate)) Ht). }
  intro t; split.
  - apply (Indexed.mu_unfold RI (fun X i => F i X) HM HN i Hi).
  - apply (Indexed.rolled_mu_inclusion RI (fun X i => F i X) HM HN i Hi).
Qed.

Print Assumptions small_fixed_point_rolled_equiv.
