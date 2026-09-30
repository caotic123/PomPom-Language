(* Semantic close-case typing, including motives at arbitrary levels. *)
From Stdlib Require Import List Arith Lia.
Require Export nameless.DBSemanticPrimitiveRules.
Import ListNotations Full.

Lemma semantic_close_case : forall k IT RI D G i Q b x,
  small_interp IT RI -> semantic_value D (Def IT) -> semantic_value G (Def IT) -> semantic_value i IT ->
  semantic_value Q (TPi (CloseAt IT D G i) (TSort k)) ->
  semantic_value b (close_case_method IT D G i Q) -> semantic_value x (CloseAt IT D G i) ->
  semantic_value (TCloseCase k IT D G i Q b x) (TApp Q x).
Proof.
  intros k IT RI D G i Q b x HI HD HG Hi HQ Hb Hx.
  pose proof (small_type_candidate _ _ HI) as CRI.
  pose proof (semantic_definition IT RI D HI HD) as HDC.
  pose proof (semantic_definition IT RI G HI HG) as HGC.
  pose proof (small_semantic_member _ _ _ Hi HI) as Hic.
  pose proof (semantic_close_family IT RI D G HI HDC HGC i Hic) as HC.
  set (Payload := definition_meaning RI D i (definition_fixed_point RI G)).
  assert (HA : small_interp (payload IT D G i) Payload).
  { eapply semantic_interpretation_as; [exact HI|exact (proj2 HDC i Hic)
      |exact (computable_definition_meaning RI CRI D HDC i Hic)
      |unfold carrier; apply full_SN_close; [exact (type_interp_normalizing _ _ _ HI)|exact (proj1 HGC)|exact (proj1 HGC)]
      |exact (semantic_carrier_family IT RI G HI HGC)]. }
  assert (HTQ : calculus_interp (S k) (TPi (CloseAt IT D G i) (TSort k))
    (dependent_function (rolled_elements Payload) (fun _ => calculus_type k))).
  { apply calculus_pi_interp; [exact (small_type_in_universe _ _ HC (S k))|].
    intros y Hy; apply calculus_sort_interp; lia. }
  pose proof (semantic_value_member _ _ _ _ HQ HTQ) as HQc.
  set (Result := fun y => calculus_elements k (TApp Q y)).
  assert (HT : forall y, rolled_elements Payload y -> calculus_interp k (TApp Q y) (Result y)).
  { intros y Hy; apply calculus_interp_canonical; exact (proj2 HQc y Hy). }
  assert (HTb : calculus_interp k (close_case_method IT D G i Q)
    (dependent_function Payload (fun u => Result (TIn u)))).
  { apply calculus_pi_interp; [exact (small_type_in_universe _ _ HA k)|].
    intros u Hu; cbn [subst]; rewrite subst_lift_zero, lift_zero_id; apply HT.
    now apply rolled_elements_intro. }
  pose proof (semantic_value_member _ _ _ _ Hb HTb) as Hbc.
  pose proof (small_semantic_member _ _ _ Hx HC) as Hxc.
  pose proof (small_type_candidate _ _ HA) as CA.
  pose proof (rolled_elements_candidate _ CA) as CC.
  exists k, (Result x); split; [exact (HT x Hxc)|].
  eapply close_case_computable with (Payload:=Payload).
  - exact CA.
  - intros y Hy; exact (calculus_interp_candidate _ _ _ (HT y Hy)).
  - intros y z Hy HR; eapply calculus_interp_unique;
      [exact (HT y Hy)|exact (HT z (candidate_reduct CC Hy HR))|].
    apply reductions_conversion, red_star_TApp; [constructor|now apply rtc_one].
  - constructor; [exact (type_interp_normalizing _ _ _ HI)|].
    constructor; [exact (proj1 HDC)|constructor; [exact (proj1 HGC)|]].
    constructor; [exact (candidate_normalizing CRI Hic)|].
    constructor; [exact (proj1 HQc)|constructor; [exact (proj1 Hbc)|constructor]].
  - exact (proj2 Hbc).
  - exact Hxc.
Qed.

Print Assumptions semantic_close_case.
