(* Computability of switching, including reductions in all annotations. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBEnumComputability.
Import ListNotations Full.

Definition calculus_value n t A := exists R, calculus_interp n A R /\ R t.
Lemma calculus_value_member : forall n t A R,
  calculus_value n t A -> calculus_interp n A R -> R t.
Proof.
  intros n t A R [S [HS Ht]] HR.
  apply (calculus_interp_unique _ _ _ _ _ _ HS HR (cv_refl _)); exact Ht.
Qed.
Lemma calculus_value_conversion : forall n t A B,
  calculus_value n t A -> calculus_type n B -> conv A B -> calculus_value n t B.
Proof.
  intros n t A B [R [HR Ht]] HB HC; exists R; split; [|exact Ht].
  eapply type_interp_conversion; [exact HR|exact (candidate_normalizing (calculus_type_candidate n) HB)|exact HC].
Qed.
Lemma calculus_value_reductions : forall n t A u,
  calculus_value n t A -> rtc reduction t u -> calculus_value n u A.
Proof.
  intros n t A u [R [HR Ht]] Htu; exists R; split; [exact HR|].
  exact (candidate_reducts R (calculus_interp_candidate _ _ _ HR) _ _ Htu Ht).
Qed.
Lemma calculus_value_type_reductions : forall n t A B,
  calculus_value n t A -> rtc reduction A B -> calculus_value n t B.
Proof.
  intros n t A B [R [HR Ht]] HAB; exists R; split; [|exact Ht].
  eapply type_interp_reductions; eassumption.
Qed.
Lemma succ_reductions : forall u t, rtc reduction (TESucc u) t ->
  exists v, t = TESucc v /\ rtc reduction u v.
Proof.
  apply DBInterpretationComputability.reduces_unary; intros u t H;
    inversion H; subst; [discriminate|].
  eexists; split; [reflexivity|now apply rtc_one].
Qed.
Lemma extended_elements_succ : forall R, candidate R -> forall e,
  extended_elements R (TESucc e) -> R e.
Proof.
  intros R CR.
  assert (CQ : candidate (fun t => full_SN t /\
    forall n, rtc reduction t (TESucc n) -> R n)).
  { constructor.
    - tauto.
    - intros t u [HS HT] HR; split; [exact (Acc_inv HS HR)|].
      intros n Hn; apply HT; eapply rtc_step; eassumption.
    - intros t HN HR; split; [constructor; intros u HU; exact (proj1 (HR u HU))|].
      intros n Hn; inversion Hn; subst; [contradiction|].
      eapply (proj2 (HR _ H)); eassumption. }
  intros e He; refine (proj2 (He _ CQ _ ) e rtc_refl).
  intros t [->|[u [-> Hu]]]; split.
  - exact full_SN_zero.
  - intros n Hn; assert (HZ : normal_form TEZero) by
      (intros z Hz; inversion Hz; discriminate).
    pose proof (normal_reductions_identity _ _ HZ Hn); discriminate.
  - apply full_SN_succ; exact (candidate_normalizing CR Hu).
  - intros n Hn; destruct (succ_reductions _ _ Hn) as [v [HE HR]].
    inversion HE; subst; exact (candidate_reducts R CR _ _ HR Hu).
Qed.

Definition switch_roots E := forall E', rtc reduction E E' -> forall n k P p e,
  full_SN P -> enum_family n E' P ->
  calculus_value n p (TEPi k E' P) -> enum_elements E' e -> forall v,
  root_step (TSwitch k E' P p e) = Some v -> calculus_value n v (TApp P e).
Lemma switch_roots_reductions : forall E, switch_roots E -> forall E',
  rtc reduction E E' -> switch_roots E'.
Proof. intros E H E' HR E'' HR'; apply H; eapply rtc_trans; eassumption. Qed.
Lemma switch_from_roots : forall E, full_SN E -> switch_roots E -> forall n k P p e,
  full_SN P -> enum_family n E P ->
  calculus_value n p (TEPi k E P) -> enum_elements E e ->
  calculus_value n (TSwitch k E P p e) (TApp P e).
Proof.
  intros E HE HR n k P p e HP HF [RP [HT Hpv]] He.
  pose proof (calculus_interp_candidate _ _ _ HT) as CP.
  pose proof (enum_elements_candidate E) as CE.
  destruct (HF e He) as [R HPe].
  exists R; split; [exact HPe|].
  apply computability_by_head_expansion; [exact (calculus_interp_candidate _ _ _ HPe)| | |].
  - cbn [term_children]; constructor; [exact HE|constructor; [exact HP|]].
    constructor; [exact (candidate_normalizing CP Hpv)|].
    constructor; [exact (candidate_normalizing CE He)|constructor].
  - intros t Ht; inversion Ht; exact I.
  - intros t v Ht Hv; inversion Ht; subst; inversion Hv; subst.
    assert (HF' : enum_family n E' P') by (eapply enum_family_reductions; eassumption).
    assert (Hp' : calculus_value n p' (TEPi k E' P')).
    { eapply calculus_value_type_reductions with (A:=TEPi k E P);
        [eapply calculus_value_reductions with (t:=p); [exists RP; auto|exact H7]|now apply red_star_TEPi]. }
    assert (He' : enum_elements E' e').
    { apply (enum_elements_conversion _ _ (reductions_conversion _ _ H5));
      exact (candidate_reducts _ CE _ _ H8 He). }
    assert (Hroot : calculus_value n v (TApp P' e')).
    { eapply HR; [exact H5|exact (full_SN_reductions _ HP _ H6)|exact HF'|exact Hp'|exact He'|eassumption]. }
    destruct Hroot as [S [HS HvS]].
    apply (calculus_interp_unique _ _ _ _ _ _ HS HPe);
      [apply cv_sym, reductions_conversion; now apply red_star_TApp|exact HvS].
Qed.

Lemma switch_product_components : forall n k tag E P p ps,
  full_SN tag -> enumeration_computable E -> full_SN P ->
  enum_family n (TConsE tag E) P ->
  calculus_value n (TPair p ps) (TEPi k (TConsE tag E) P) ->
  calculus_value n p (TApp P TEZero) /\
  calculus_value n ps (TEPi k E (enum_tail_family P)).
Proof.
  intros n k tag E P p ps Htag HE HP HF [R [HR Hpair]].
  pose proof (enumeration_computable_normalizing _ HE) as HSE.
  pose proof (HF _ (enum_zero_computable _ _ Htag HSE)) as HA.
  destruct (enum_tail_family_computable n tag E P Htag HSE HF) as [HS HFtail].
  pose proof (epi_computable E HE n k _ HS HFtail) as HB.
  pose proof (calculus_interp_canonical n _ HA) as IA.
  pose proof (calculus_interp_canonical n _ HB) as IB.
  pose proof (calculus_product_interp _ _ _ _ _ IA IB) as IP.
  assert (HC : conv (TEPi k (TConsE tag E) P)
    (product (TApp P TEZero) (TEPi k E (enum_tail_family P)))).
  { apply reductions_conversion, rtc_one, red_root; reflexivity. }
  pose proof (proj1 (calculus_interp_unique _ _ _ _ _ _ HR IP HC _) Hpair) as Hprod.
  destruct (dependent_pair_value _ _ (calculus_interp_candidate _ _ _ IA)
    (fun _ _ => calculus_interp_candidate _ _ _ IB)
    (fun _ _ _ _ _ => iff_refl _) _ _ Hprod) as [Ha Hb].
  split; [exists (calculus_elements n (TApp P TEZero))|exists (calculus_elements n (TEPi k E (enum_tail_family P)))]; auto.
Qed.

Theorem computable_switch_roots : forall E, enumeration_computable E -> switch_roots E.
Proof.
  intros E H; induction H; intros Eout RE n k P p e HP HF Hp He v HV.
  - pose proof (normal_reductions_identity _ _ nil_enum_normal RE); subst Eout.
    discriminate.
  - destruct (cons_enum_reductions _ _ _ RE) as [tag' [E' [-> [RT RE']]]].
    pose proof (full_SN_reductions _ H _ RT) as HT'.
    pose proof (candidate_reducts _ enumeration_computable_candidate _ _ RE' H0) as HE'.
    pose proof (enumeration_computable_normalizing _ HE') as HSE'.
    destruct p; cbn [root_step] in HV; try discriminate.
    destruct e; cbn [root_step] in HV; try discriminate; inversion HV; subst v.
    + exact (proj1 (switch_product_components _ _ _ _ _ _ _ HT' HE' HP HF Hp)).
    + destruct (switch_product_components _ _ _ _ _ _ _ HT' HE' HP HF Hp) as [Hp0 Hps].
      pose proof (proj1 (enum_elements_cons _ _ HT' HSE' _) He) as Hsucc.
      pose proof (extended_elements_succ _ (enum_elements_candidate E') _ Hsucc) as Hidx.
      destruct (enum_tail_family_computable n tag' E' P HT' HSE' HF) as [HS HFtail].
      eapply calculus_value_conversion.
      * apply switch_from_roots; [exact HSE'|eapply switch_roots_reductions; eassumption|exact HS|exact HFtail|exact Hps|exact Hidx].
      * apply HF; exact He.
      * apply reductions_conversion, rtc_one, red_root; cbn [root_step enum_tail_family]; now rewrite enum_tail_subst.
  - eapply IHenumeration_computable; [eapply rtc_step; eassumption|exact HP|exact HF|exact Hp|exact He|exact HV].
  - inversion RE; subst.
    + destruct Eout; cbn [neutral root_step] in *; contradiction || discriminate.
    + eapply H1; eassumption.
Qed.
Theorem switch_computable : forall E, enumeration_computable E -> forall n k P p e,
  full_SN P -> enum_family n E P ->
  calculus_value n p (TEPi k E P) -> enum_elements E e ->
  calculus_value n (TSwitch k E P p e) (TApp P e).
Proof.
  intros E HE; apply switch_from_roots;
    [now apply enumeration_computable_normalizing|now apply computable_switch_roots].
Qed.

Print Assumptions switch_computable.
