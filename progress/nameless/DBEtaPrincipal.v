(* Eta contraction for functions with a stable principal type. Type changes
   are inverted and strengthened without assuming eta subject reduction. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBTypeComparison.
Import ListNotations.

Definition stable_principal Gamma f S := forall A T,
  typing (A::Gamma) (lift 1 0 f) T -> type_comparison (lift 1 0 S) T.

Lemma stable_principal_conversion : forall Gamma f S T,
  stable_principal Gamma f S -> conv S T -> stable_principal Gamma f T.
Proof.
  intros Gamma f S T HS HC A U HU.
  eapply comparison_left_conversion; [exact (HS A U HU)|].
  apply cv_sym; now apply conversion_lift.
Qed.

Lemma stable_principal_application : forall Gamma f a A B,
  stable_principal Gamma f (TPi A B) ->
  stable_principal Gamma (TApp f a) (subst a 0 B).
Proof.
  intros Gamma f a A B HP C T HT.
  destruct (application_change_generation _ _ _ HT _ _ eq_refl)
    as [U [V [Hf [Ha HC]]]].
  destruct (comparison_pi_inversion _ _ _ _ (HP C _ Hf)) as [_ Hcod].
  pose proof (comparison_subst _ _ Hcod (lift 1 0 a) 0) as H.
  rewrite <- lift_subst_zero_comm in H.
  eapply comparison_transitive; [exact H|now apply type_change_comparison in HC].
Qed.

Definition explicit_principal (t : term) : option term :=
  match t with
  | TMuI IT _ | TClose IT _ _ => Some (Family IT)
  | TSwitch _ _ P _ e => Some (TApp P e)
  | TInd _ _ P _ i x => Some (TApp P (TPair i x))
  | THyps IT D X P _ xs => Some (TIAll IT D X xs P)
  | TCloseCase _ _ _ _ _ Q _ x => Some (TApp Q x)
  | TCloseInd _ _ P _ F i x => Some (TApp (TApp (TApp P F) i) x)
  | _ => None
  end.

Lemma explicit_principal_generation : forall Gamma t T,
  typing Gamma t T -> forall S, explicit_principal t = Some S ->
  typing Gamma t S /\ type_comparison S T.
Proof.
  intros Gamma t T H; induction H; intros S HE; cbn [explicit_principal] in HE; try discriminate.
  all: try solve [inversion HE; subst; split; [econstructor; eassumption|apply cmp_conversion, cv_refl]].
  - destruct (IHtyping1 _ HE) as [HS HC]; split; [exact HS|].
    eapply comparison_right_conversion; eassumption.
  - destruct (IHtyping _ HE) as [HS HC]; split; [exact HS|].
    eapply comparison_transitive; [exact HC|apply comparison_universe; now apply ul_sort].
  - destruct (IHtyping1 _ HE) as [HS HC]; split; [exact HS|].
    eapply comparison_transitive; [exact HC|apply comparison_universe; now apply ul_pi].
Qed.

Lemma explicit_principal_lift : forall t S d c,
  explicit_principal t = Some S ->
  explicit_principal (lift d c t) = Some (lift d c S).
Proof.
  destruct t; intros S d c H; cbn [explicit_principal] in H; try discriminate;
    inversion H; subst; reflexivity.
Qed.

Lemma explicit_stable_principal : forall Gamma t S,
  explicit_principal t = Some S -> stable_principal Gamma t S.
Proof.
  intros Gamma t S HE A T HT.
  exact (proj2 (explicit_principal_generation _ _ _ HT _ (explicit_principal_lift _ _ 1 0 HE))).
Qed.

Theorem eta_principal_preservation : forall Gamma f S,
  typing Gamma f S -> stable_principal Gamma f S -> forall T,
  typing Gamma (TLam (TApp (lift 1 0 f) (TVar 0))) T -> typing Gamma f T.
Proof.
  intros Gamma f S Hf Hprincipal T HT.
  destruct (lambda_generation _ _ _ HT _ eq_refl) as [A [B [k [HP [Hb HPT]]]]].
  destruct (pi_components _ _ _ HP _ _ eq_refl) as [ja [jb [HA HB]]].
  destruct (application_change_generation _ _ _ Hb _ _ eq_refl)
    as [U [V [Hfun [Harg Hbody]]]].
  pose proof (Hprincipal A _ Hfun) as HfunCmp.
  destruct (comparison_pi_source _ _ HfunCmp _ _ (cv_refl _)) as [C0 [D0 HC0]].
  pose proof (conversion_subst _ _ HC0 TUnit 0) as HSC.
  cbn [subst] in HSC; rewrite subst_lift_cancel in HSC.
  destruct (type_correctness _ _ _ Hf) as [j HS].
  destruct (typed_pi_view _ _ _ _ _ HS HSC) as [C [D [HQ [HC [HD HSC']]]]].
  destruct (pi_components _ _ _ HQ _ _ eq_refl) as [jc [jd [HCf HDf]]].
  assert (HfPi : typing Gamma f (TPi C D)) by (eapply ty_conv; eassumption).
  assert (HfunCmp' : type_comparison (TPi (lift 1 0 C) (lift 1 1 D)) (TPi U V)).
  { eapply comparison_left_conversion; [exact HfunCmp|].
    apply cv_sym; exact (conversion_lift _ _ HSC' 1 0). }
  destruct (comparison_pi_inversion _ _ _ _ HfunCmp') as [HDom HCod].
  destruct (variable_change_generation _ _ _ Harg _ eq_refl) as [A0 [HA0 HArg]].
  cbn [nth_error] in HA0; inversion HA0; subst A0.
  assert (HAC : type_comparison A C).
  { pose proof (comparison_transitive _ _ _ (type_change_comparison _ _ _ HArg) HDom) as H.
    pose proof (comparison_subst _ _ H TUnit 0) as H'; now rewrite !subst_lift_cancel in H'. }
  assert (HACtyped : type_change Gamma A C) by (apply comparison_realization; eauto; eexists; eassumption).
  assert (HDB : type_comparison D B).
  { pose proof (comparison_subst _ _ HCod (TVar 0) 0) as H.
    rewrite subst_eta_beta_cancel in H.
    eapply comparison_transitive; [exact H|now apply type_change_comparison in Hbody]. }
  assert (HDBtyped : type_change (A::Gamma) D B).
  { apply comparison_realization; [exact HDB| |exists jb; exact HB].
    exists jd; eapply type_change_narrowing; eassumption. }
  assert (Hnew : typing Gamma f (TPi A B)).
  { eapply type_change_typing; [eapply type_change_pi; [exact HACtyped|exists jd; exact HDf|exact HDBtyped]|exact HfPi]. }
  destruct (type_correctness _ _ _ HT) as [l HTf]; eapply ty_conv; eassumption.
Qed.

Lemma variable_stable_principal : forall Gamma n S,
  nth_error Gamma n = Some S ->
  stable_principal Gamma (TVar n) (lift (Datatypes.S n) 0 S).
Proof.
  intros Gamma n S Hlookup A T HT.
  change (typing (A::Gamma) (TVar (Datatypes.S n)) T) in HT.
  destruct (variable_change_generation _ _ _ HT _ eq_refl) as [U [HU HC]].
  cbn [nth_error] in HU; rewrite Hlookup in HU; inversion HU; subst U.
  rewrite lift_fuse_zero by lia; now apply type_change_comparison in HC.
Qed.

Theorem eta_variable_preservation : forall Gamma n T,
  typing Gamma (TLam (TApp (lift 1 0 (TVar n)) (TVar 0))) T ->
  typing Gamma (TVar n) T.
Proof.
  intros Gamma n T HT.
  destruct (lambda_generation _ _ _ HT _ eq_refl) as [A [B [k [HP [Hb HC]]]]].
  destruct (application_change_generation _ _ _ Hb _ _ eq_refl) as [U [V [HF _]]].
  change (typing (A::Gamma) (TVar (Datatypes.S n)) (TPi U V)) in HF.
  destruct (variable_change_generation _ _ _ HF _ eq_refl) as [S [HS _]].
  cbn [nth_error] in HS.
  eapply eta_principal_preservation; [eapply smart_var; [eauto using typing_context|exact HS]|now apply variable_stable_principal|exact HT].
Qed.

Print Assumptions eta_principal_preservation.
Print Assumptions eta_variable_preservation.
