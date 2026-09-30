From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBSubstitution.
Import ListNotations.

Lemma universe_le_typing : forall Gamma t A B,
  typing Gamma t A -> universe_le A B -> type_wf Gamma B -> typing Gamma t B.
Proof.
  intros Gamma t A B Ht HU [k HB]; destruct HU.
  - exact Ht.
  - eapply ty_cumul; eassumption.
  - destruct (type_correctness _ _ _ Ht) as [j HA].
    eapply ty_cumul_fun; eassumption.
Qed.

Lemma pi_components : forall Gamma t T, typing Gamma t T -> forall A B,
  t = TPi A B -> exists j k, typing Gamma A (TSort j) /\ typing (A::Gamma) B (TSort k).
Proof.
  intros Gamma t T H; induction H; intros AA BB Heq; try discriminate; eauto.
  inversion Heq; subst; eauto.
Qed.
Lemma sigma_components : forall Gamma t T, typing Gamma t T -> forall A B,
  t = TSigma A B -> exists j k, typing Gamma A (TSort j) /\ typing (A::Gamma) B (TSort k).
Proof.
  intros Gamma t T H; induction H; intros AA BB Heq; try discriminate; eauto.
  inversion Heq; subst; eauto.
Qed.

Lemma smart_var : forall Gamma n A,
  wf Gamma -> nth_error Gamma n = Some A -> typing Gamma (TVar n) (lift (S n) 0 A).
Proof.
  intros Gamma n A Hwf Hn. destruct (lookup_formation _ Hwf _ _ Hn) as [k HA].
  eapply ty_var; eassumption.
Qed.
Lemma smart_app : forall Gamma A B f a k,
  typing Gamma (TPi A B) (TSort k) -> typing Gamma f (TPi A B) -> typing Gamma a A ->
  typing Gamma (TApp f a) (subst a 0 B).
Proof.
  intros Gamma A B f a k HPi Hf Ha.
  destruct (pi_components _ _ _ HPi _ _ eq_refl) as [j [l [HA HB]]].
  eapply ty_app; try eassumption. exact (substitution _ _ _ _ _ HB Ha).
Qed.
Lemma regular_application : forall Gamma A B f a,
  typing Gamma f (TPi A B) -> typing Gamma a A -> typing Gamma (TApp f a) (subst a 0 B).
Proof.
  intros Gamma A B f a Hf Ha. destruct (type_correctness _ _ _ Hf) as [k HPi].
  eapply smart_app; eassumption.
Qed.
Lemma smart_fst : forall Gamma A B p k,
  typing Gamma (TSigma A B) (TSort k) -> typing Gamma p (TSigma A B) -> typing Gamma (TFst p) A.
Proof.
  intros Gamma A B p k HS Hp.
  destruct (sigma_components _ _ _ HS _ _ eq_refl) as [j [l [HA HB]]]. eapply ty_fst; eassumption.
Qed.
Lemma smart_snd : forall Gamma A B p k,
  typing Gamma (TSigma A B) (TSort k) -> typing Gamma p (TSigma A B) ->
  typing Gamma (TSnd p) (subst (TFst p) 0 B).
Proof.
  intros Gamma A B p k HS Hp.
  destruct (sigma_components _ _ _ HS _ _ eq_refl) as [j [l [HA HB]]].
  eapply ty_snd; try eassumption.
  apply (substitution _ _ _ _ _ HB (smart_fst _ _ _ _ _ HS Hp)).
Qed.

Lemma family_formation : forall Gamma IT,
  typing Gamma IT (TSort 0) -> typing Gamma (Family IT) (TSort 1).
Proof.
  intros Gamma IT HIT. change (TSort 1) with (TSort (Nat.max 0 1)).
  apply ty_pi; [exact HIT|apply ty_sort;eapply wf_cons;eauto using typing_context].
Qed.
Lemma smart_mui : forall Gamma IT D,
  typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) -> typing Gamma (TMuI IT D) (Family IT).
Proof. intros; eapply ty_mui; eauto using family_formation. Qed.
Lemma smart_close : forall Gamma IT F G,
  typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) -> typing Gamma G (Def IT) ->
  typing Gamma (TClose IT F G) (Family IT).
Proof. intros; eapply ty_close; eauto using family_formation. Qed.
Lemma mu_at_formation : forall Gamma IT D i,
  typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) -> typing Gamma i IT ->
  typing Gamma (MuAt IT D i) (TSort 0).
Proof.
  intros Gamma IT D i HIT HD Hi.
  exact (regular_application _ _ _ _ _ (smart_mui _ _ _ HIT HD) Hi).
Qed.
Lemma close_at_formation : forall Gamma IT F G i,
  typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) -> typing Gamma G (Def IT) -> typing Gamma i IT ->
  typing Gamma (CloseAt IT F G i) (TSort 0).
Proof.
  intros Gamma IT F G i HIT HF HG Hi.
  exact (regular_application _ _ _ _ _ (smart_close _ _ _ _ HIT HF HG) Hi).
Qed.
Lemma total_formation : forall Gamma IT X,
  typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) ->
  typing Gamma (total IT X) (TSort 0).
Proof.
  intros Gamma IT X HIT HX. change (TSort 0) with (TSort (Nat.max 0 0)).
  apply ty_sigma; [exact HIT|].
  pose proof (weakening _ _ _ _ _ HX HIT) as HX'. rewrite lift_Family in HX'.
  assert (Hv : typing (IT::Gamma) (TVar 0) (lift 1 0 IT)).
  { apply smart_var; [eapply wf_cons;eauto using typing_context|reflexivity]. }
  exact (regular_application _ _ _ _ _ HX' Hv).
Qed.
Lemma total_pair : forall Gamma IT X i x,
  typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) ->
  typing Gamma i IT -> typing Gamma x (TApp X i) -> typing Gamma (TPair i x) (total IT X).
Proof.
  intros Gamma IT X i x HIT HX Hi Hx.
  eapply ty_pair; [apply total_formation;eassumption|exact Hi|].
  cbn [subst]. now rewrite subst_lift_zero, lift_zero_id.
Qed.
Lemma motive_application : forall Gamma IT X P i x,
  typing Gamma IT (TSort 0) -> typing Gamma X (Family IT) -> typing Gamma P (motive IT X) ->
  typing Gamma i IT -> typing Gamma x (TApp X i) -> typing Gamma (TApp P (TPair i x)) (TSort 0).
Proof.
  intros Gamma IT X P i x HIT HX HP Hi Hx.
  exact (regular_application _ _ _ _ _ HP (total_pair _ _ _ _ _ HIT HX Hi Hx)).
Qed.

Lemma subst_lift_prefix : forall t u n c, c <= n ->
  subst u c (lift (S n) 0 t) = lift n 0 t.
Proof.
  intros t u n c Hcn. replace (lift (S n) 0 t) with (lift 1 c (lift n 0 t)) by
    (apply lift_fuse_zero;exact Hcn). apply subst_lift_cancel.
Qed.
Lemma close_motive_application : forall Gamma IT G P F i x,
  typing Gamma P (close_motive IT G) -> typing Gamma F (Def IT) -> typing Gamma i IT ->
  typing Gamma x (CloseAt IT F G i) -> typing Gamma (TApp (TApp (TApp P F) i) x) (TSort 0).
Proof.
  intros Gamma IT G P F i x HP HF Hi Hx.
  pose proof (regular_application _ _ _ _ _ HP HF) as H1.
  cbn [close_motive subst CloseAt] in H1.
  rewrite !subst_lift_prefix in H1 by lia. rewrite !lift_zero_id in H1. cbn [Nat.ltb Nat.leb Nat.eqb] in H1.
  pose proof (regular_application _ _ _ _ _ H1 Hi) as H2.
  cbn [subst Nat.ltb Nat.leb Nat.eqb] in H2. rewrite !subst_lift_zero, !lift_zero_id in H2.
  exact (regular_application _ _ _ _ _ H2 Hx).
Qed.

Lemma smart_unit : forall Gamma, wf Gamma -> typing Gamma TUnit TUnitT.
Proof.
  intros; eapply ty_unit with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_tag : forall Gamma s, wf Gamma -> typing Gamma (TTag s) TUId.
Proof.
  intros; eapply ty_tag with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_nile : forall Gamma, wf Gamma -> typing Gamma TNilE TEnumU.
Proof.
  intros; eapply ty_nile with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_conse : forall Gamma tag E,
    typing Gamma tag TUId -> typing Gamma E TEnumU ->
    typing Gamma (TConsE tag E) TEnumU.
Proof.
  intros; eapply ty_conse with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_zero : forall Gamma tag E,
    typing Gamma tag TUId -> typing Gamma E TEnumU ->
    typing Gamma TEZero (TEnumT (TConsE tag E)).
Proof.
  intros; eapply ty_zero with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_succ : forall Gamma tag E n,
    typing Gamma tag TUId -> typing Gamma E TEnumU ->
    typing Gamma n (TEnumT E) ->
    typing Gamma (TESucc n) (TEnumT (TConsE tag E)).
Proof.
  intros; eapply ty_succ with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_switch : forall Gamma k E P p e,
    typing Gamma E TEnumU ->
    typing Gamma P (TPi (TEnumT E) (TSort k)) ->
    typing Gamma p (TEPi k E P) -> typing Gamma e (TEnumT E) ->
    typing Gamma (TSwitch k E P p e) (TApp P e).
Proof.
  intros; eapply ty_switch with (formation_level:=k); try eassumption.
  match goal with HF : typing ?G ?f (TPi ?A ?B), HA : typing ?G ?a ?A |- typing ?G (TApp ?f ?a) _ =>
    exact (regular_application _ _ _ _ _ HF HA) end.
Qed.

Lemma smart_ivar : forall Gamma IT i,
    typing Gamma IT (TSort 0) -> typing Gamma i IT ->
    typing Gamma (TIVar i) (TIDesc IT).
Proof.
  intros; eapply ty_ivar with (formation_level:=1); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_i1 : forall Gamma IT,
    typing Gamma IT (TSort 0) -> typing Gamma TI1 (TIDesc IT).
Proof.
  intros; eapply ty_i1 with (formation_level:=1); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_ibot : forall Gamma IT,
    typing Gamma IT (TSort 0) -> typing Gamma TIBot (TIDesc IT).
Proof.
  intros; eapply ty_ibot with (formation_level:=1); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_iprod : forall Gamma IT A B,
    typing Gamma IT (TSort 0) ->
    typing Gamma A (TIDesc IT) -> typing Gamma B (TIDesc IT) ->
    typing Gamma (TIProd A B) (TIDesc IT).
Proof.
  intros; eapply ty_iprod with (formation_level:=1); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_ipi : forall Gamma IT A D,
    typing Gamma IT (TSort 0) -> typing Gamma A (TSort 0) ->
    typing Gamma D (arrow A (TIDesc IT)) ->
    typing Gamma (TIPi A D) (TIDesc IT).
Proof.
  intros; eapply ty_ipi with (formation_level:=1); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_isig : forall Gamma IT A D,
    typing Gamma IT (TSort 0) -> typing Gamma A (TSort 0) ->
    typing Gamma D (arrow A (TIDesc IT)) ->
    typing Gamma (TISig A D) (TIDesc IT).
Proof.
  intros; eapply ty_isig with (formation_level:=1); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_ichoice : forall Gamma IT E D,
    typing Gamma IT (TSort 0) -> typing Gamma E TEnumU ->
    typing Gamma D (arrow (TEnumT E) (TIDesc IT)) ->
    typing Gamma (TIChoice E D) (TIDesc IT).
Proof.
  intros; eapply ty_ichoice with (formation_level:=1); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_in_mui : forall Gamma IT D i xs,
    typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
    typing Gamma i IT -> typing Gamma xs (TInterp IT (TApp D i) (TMuI IT D)) ->
    typing Gamma (TIn xs) (MuAt IT D i).
Proof.
  intros; eapply ty_in_mui with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_hyps : forall Gamma IT D X P h xs,
    typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) ->
    typing Gamma X (Family IT) -> typing Gamma P (motive IT X) ->
    typing Gamma h (recursive_method IT X P) ->
    typing Gamma xs (TInterp IT D X) ->
    typing Gamma (THyps IT D X P h xs) (TIAll IT D X xs P).
Proof.
  intros; eapply ty_hyps with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_ind : forall Gamma IT D P st i x,
    typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
    typing Gamma P (motive IT (TMuI IT D)) ->
    typing Gamma st (mu_ind_method IT D P) ->
    typing Gamma i IT -> typing Gamma x (MuAt IT D i) ->
    typing Gamma (TInd IT D P st i x) (TApp P (TPair i x)).
Proof.
  intros; eapply ty_ind with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_in_close : forall Gamma IT F G i xs,
    typing Gamma IT (TSort 0) ->
    typing Gamma F (Def IT) -> typing Gamma G (Def IT) ->
    typing Gamma i IT -> typing Gamma xs (payload IT F G i) ->
    typing Gamma (TIn xs) (CloseAt IT F G i).
Proof.
  intros; eapply ty_in_close with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.

Lemma smart_close_case : forall Gamma k IT F G i Q b x,
    typing Gamma IT (TSort 0) ->
    typing Gamma F (Def IT) -> typing Gamma G (Def IT) ->
    typing Gamma i IT ->
    typing Gamma Q (TPi (CloseAt IT F G i) (TSort k)) ->
    typing Gamma b (close_case_method IT F G i Q) ->
    typing Gamma x (CloseAt IT F G i) ->
    typing Gamma (TCloseCase k IT F G i Q b x) (TApp Q x).
Proof.
  intros; eapply ty_close_case with (formation_level:=k); try eassumption.
  match goal with HF : typing ?G ?f (TPi ?A ?B), HA : typing ?G ?a ?A |- typing ?G (TApp ?f ?a) _ =>
    exact (regular_application _ _ _ _ _ HF HA) end.
Qed.

Lemma smart_close_ind : forall Gamma IT G P st F i x,
    typing Gamma IT (TSort 0) -> typing Gamma G (Def IT) ->
    typing Gamma P (close_motive IT G) ->
    typing Gamma st (close_ind_method IT G P) ->
    typing Gamma F (Def IT) -> typing Gamma i IT ->
    typing Gamma x (CloseAt IT F G i) ->
    typing Gamma (TCloseInd IT G P st F i x)
      (TApp (TApp (TApp P F) i) x).
Proof.
  intros; eapply ty_close_ind with (formation_level:=0); try eassumption.
  eauto 8 using ty_unitT, ty_uid, ty_enumu, ty_enumt, ty_idesc, ty_iall,
    typing_context, smart_conse, smart_mui, mu_at_formation, close_at_formation,
    motive_application, close_motive_application.
Qed.
