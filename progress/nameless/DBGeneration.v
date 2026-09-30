From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBContexts.
Import ListNotations.

Inductive head_tag :=
| h_sort | h_pi | h_sigma | h_unitT | h_unit | h_uid | h_tag
| h_enumu | h_nile | h_conse | h_enumt | h_zero | h_succ
| h_idesc | h_ivar | h_i1 | h_ibot | h_iprod | h_ipi | h_isig | h_ichoice
| h_mui | h_muapp | h_close | h_closeapp | h_in.

Definition term_head t :=
  match t with
  | TSort _ => Some h_sort | TPi _ _ => Some h_pi
  | TSigma _ _ => Some h_sigma | TUnitT => Some h_unitT
  | TUnit => Some h_unit | TUId => Some h_uid | TTag _ => Some h_tag
  | TEnumU => Some h_enumu | TNilE => Some h_nile | TConsE _ _ => Some h_conse
  | TEnumT _ => Some h_enumt | TEZero => Some h_zero | TESucc _ => Some h_succ
  | TIDesc _ => Some h_idesc | TIVar _ => Some h_ivar
  | TI1 => Some h_i1 | TIBot => Some h_ibot | TIProd _ _ => Some h_iprod
  | TIPi _ _ => Some h_ipi | TISig _ _ => Some h_isig | TIChoice _ _ => Some h_ichoice
  | TMuI _ _ => Some h_mui | TApp (TMuI _ _) _ => Some h_muapp
  | TClose _ _ _ => Some h_close | TApp (TClose _ _ _) _ => Some h_closeapp
  | TIn _ => Some h_in | _ => None
  end.

Lemma root_has_no_rigid_head : forall t u,
  root_step t = Some u -> term_head t = None.
Proof.
  destruct t; intros u H; cbn [root_step term_head] in *;
    try discriminate; try reflexivity.
  destruct t1; cbn in *; try discriminate; reflexivity.
Qed.

Lemma reduction_head : forall t u, reduction t u ->
  forall h, term_head t = Some h -> term_head u = Some h.
Proof.
  intros t u H; induction H; intros hdtag Hhead;
    try solve [exact Hhead | discriminate Hhead].
  - pose proof (root_has_no_rigid_head _ _ H). congruence.
  - destruct f; cbn [term_head] in Hhead; try discriminate;
      specialize (IHreduction _ eq_refl); destruct f';
      cbn [term_head] in *; try congruence;
      destruct f'1; discriminate.
Qed.

Lemma reduces_head : forall t u, rtc reduction t u ->
  forall h, term_head t = Some h -> term_head u = Some h.
Proof. intros t u H; induction H; eauto using reduction_head. Qed.

Lemma conversion_head : forall t u h k, conv t u ->
  term_head t = Some h -> term_head u = Some k -> h = k.
Proof.
  intros t u h k H Ht Hu. destruct (conversion_joinable _ _ H) as [w [Htw Huw]].
  pose proof (reduces_head _ _ Htw _ Ht); pose proof (reduces_head _ _ Huw _ Hu); congruence.
Qed.

Section BinaryConversion.
Variable C : term -> term -> term.
Hypothesis redC : forall A B t, reduction (C A B) t ->
  exists A' B', t = C A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Hypothesis injC : forall A B A' B', C A B = C A' B' -> A = A' /\ B = B'.
Lemma reduces_binary : forall A B t, rtc reduction (C A B) t ->
  exists A' B', t = C A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Proof.
  intros A B t H; remember (C A B) as src eqn:E; revert A B E.
  induction H; intros A B E; subst.
  - exists A,B; repeat split;constructor.
  - destruct (redC _ _ _ H) as [A' [B' [-> [HA HB]]]].
    destruct (IHrtc _ _ eq_refl) as [A'' [B'' [-> [HA' HB']]]].
    exists A'',B''; repeat split; eauto using rtc_trans.
Qed.
Lemma conversion_binary : forall A B A' B', conv (C A B) (C A' B') -> conv A A' /\ conv B B'.
Proof.
  intros A B A' B' H. destruct (conversion_joinable _ _ H) as [w [H1 H2]].
  destruct (reduces_binary _ _ _ H1) as [U [V [-> [HU HV]]]].
  destruct (reduces_binary _ _ _ H2) as [U' [V' [HE [HU' HV']]]].
  apply injC in HE; destruct HE; subst U' V'.
  split; eapply cv_trans; [eapply reductions_conversion;eassumption|apply cv_sym;eapply reductions_conversion;eassumption|
    eapply reductions_conversion;eassumption|apply cv_sym;eapply reductions_conversion;eassumption].
Qed.
End BinaryConversion.

Lemma reduction_pi : forall A B t, reduction (TPi A B) t ->
  exists A' B', t = TPi A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Proof.
  intros A B t H; inversion H; subst; cbn [root_step] in *; try discriminate;
    eauto 7 using rtc_refl, rtc_one.
Qed.
Lemma reduction_sigma : forall A B t, reduction (TSigma A B) t ->
  exists A' B', t = TSigma A' B' /\ rtc reduction A A' /\ rtc reduction B B'.
Proof.
  intros A B t H; inversion H; subst; cbn [root_step] in *; try discriminate;
    eauto 7 using rtc_refl, rtc_one.
Qed.
Lemma conversion_pi : forall A B C D, conv (TPi A B) (TPi C D) -> conv A C /\ conv B D.
Proof. apply (conversion_binary TPi reduction_pi). intros; inversion H;auto. Qed.
Lemma conversion_sigma : forall A B C D, conv (TSigma A B) (TSigma C D) -> conv A C /\ conv B D.
Proof. apply (conversion_binary TSigma reduction_sigma). intros; inversion H;auto. Qed.

Lemma lambda_generation : forall Gamma t T, typing Gamma t T -> forall b,
  t = TLam b -> exists A B k,
  typing Gamma (TPi A B) (TSort k) /\ typing (A::Gamma) b B /\ conv (TPi A B) T.
Proof.
  intros Gamma t T H; induction H; intros body Heq; try discriminate.
  - inversion Heq; subst. exists A,B,k; repeat split;auto using cv_refl.
  - destruct (IHtyping1 _ Heq) as [X [Y [l [HP [Hb HC]]]]].
    exists X,Y,l;repeat split;try assumption; eapply cv_trans;eassumption.
  - destruct (IHtyping _ Heq) as [X [Y [l [HP [Hb HC]]]]].
    exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
  - destruct (IHtyping1 _ Heq) as [SourceA [SourceB [l [HS [Hb HC]]]]].
    destruct (conversion_pi _ _ _ _ HC) as [HA HB].
    destruct (pi_components _ _ _ HS _ _ eq_refl) as [jS [kS [HAS HBS]]].
    destruct (pi_components _ _ _ H0 _ _ eq_refl) as [jA [kB [HAA HBB]]].
    destruct (pi_components _ _ _ H1 _ _ eq_refl) as [jC [kC [HAC HCC]]].
    exists C,D,k; repeat split; auto using cv_refl.
    eapply universe_le_typing; [|exact H3|exists kC; exact HCC].
    eapply context_narrowing; [exact HAA|exact HAC|exact H2|].
    eapply ty_conv; [|exact HBB|exact HB].
    exact (context_conversion _ _ _ _ _ _ _ HAS HAA HA Hb).
Qed.
Lemma pair_generation : forall Gamma t T, typing Gamma t T -> forall a b,
  t = TPair a b -> exists A B k,
  typing Gamma (TSigma A B) (TSort k) /\ typing Gamma a A /\
  typing Gamma b (subst a 0 B) /\ conv (TSigma A B) T.
Proof.
  intros Gamma t T H; induction H; intros aa bb Heq; try discriminate.
  - inversion Heq; subst. exists A,B,k; repeat split;auto using cv_refl.
  - destruct (IHtyping1 _ _ Heq) as [X [Y [l [HP [Ha [Hb HC]]]]]].
    exists X,Y,l;repeat split;try assumption; eapply cv_trans;eassumption.
  - destruct (IHtyping _ _ Heq) as [X [Y [l [HP [Ha [Hb HC]]]]]].
    exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
  - destruct (IHtyping1 _ _ Heq) as [X [Y [l [HP [Ha [Hb HC]]]]]].
    exfalso; pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate.
Qed.
