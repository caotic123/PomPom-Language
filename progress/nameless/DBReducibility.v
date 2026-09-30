(* Reducibility infrastructure for computation normalization.
   Dependent function and pair candidates and their introductions are proved.
   A universe/description interpretation and the fundamental typing theorem
   are still required; this file does not establish typed normalization. *)
From Stdlib Require Import Bool Lia.
Require Export nameless.DBNormalization.
Require Export nameless.DBComputationSubstitution.

Definition strongly_normalizing t := Acc (fun u v => computation v u) t.
Definition neutral t :=
  match t with
  | TVar _ | TFst _ | TSnd _ | TSwitch _ _ _ _ _
  | TInd _ _ _ _ _ _ | THyps _ _ _ _ _ _
  | TCloseCase _ _ _ _ _ _ _ _ | TCloseInd _ _ _ _ _ _ _ => True
  | TApp (TMuI _ _) _ | TApp (TClose _ _ _) _ => False
  | TApp _ _ => True
  | _ => False
  end.
Record candidate (R : term -> Prop) : Prop := {
  candidate_normalizing : forall t, R t -> strongly_normalizing t;
  candidate_reduct : forall t u, R t -> computation t u -> R u;
  candidate_neutral : forall t, neutral t ->
    (forall u, computation t u -> R u) -> R t
}.
Arguments candidate_normalizing {R} _ {t} _.
Arguments candidate_reduct {R} _ {t u} _ _.
Arguments candidate_neutral {R} _ {t} _ _.

Lemma candidate_reducts : forall R, candidate R ->
  forall t u, rtc computation t u -> R t -> R u.
Proof.
  intros R HC t u H; induction H; intro HR; [exact HR|].
  apply IHrtc; eapply candidate_reduct; eassumption.
Qed.
Lemma normalizing_candidate : candidate strongly_normalizing.
Proof.
  constructor; [auto|intros t u H HR; exact (Acc_inv H HR)|].
  intros t _ H; constructor; exact H.
Qed.
Lemma candidate_variable : forall R, candidate R -> forall n, R (TVar n).
Proof.
  intros R HC n; apply (candidate_neutral HC); [exact I|].
  intros u H; inversion H; discriminate.
Qed.
Lemma neutral_not_lambda : forall t, neutral t -> not_lambda t = true.
Proof. destruct t; cbn [neutral not_lambda]; tauto. Qed.
Lemma neutral_application : forall f a, neutral f -> neutral (TApp f a).
Proof. destruct f; cbn [neutral]; tauto. Qed.
Lemma neutral_application_reduction : forall f a u, neutral f ->
  computation (TApp f a) u ->
  (exists f', computation f f' /\ u = TApp f' a) \/
  (exists a', computation a a' /\ u = TApp f a').
Proof.
  intros f a u HN HR; inversion HR; subst; eauto.
  destruct f; cbn [neutral root_step] in *; tauto || discriminate.
Qed.

Definition dependent_function (A : term -> Prop) (B : term -> term -> Prop) f :=
  strongly_normalizing f /\ forall a, A a -> B a (TApp f a).
Definition stable_family (A : term -> Prop) (B : term -> term -> Prop) :=
  forall a a', A a -> computation a a' -> forall t, B a t <-> B a' t.

Theorem dependent_function_candidate : forall A B,
  candidate A -> (forall a, A a -> candidate (B a)) -> stable_family A B ->
  candidate (dependent_function A B).
Proof.
  intros A B CA CB CS; constructor.
  - intros f [HN _]; exact HN.
  - intros f g [HN HF] HR; split; [exact (Acc_inv HN HR)|].
    intros a HA; eapply candidate_reduct; [apply CB; exact HA|apply HF; exact HA|].
    now apply cmp_TApp_f.
  - intros f HN HF; split.
    + constructor; intros u HU; exact (proj1 (HF u HU)).
    + intros a HA. pose proof (candidate_normalizing CA HA) as HS.
      revert HA; induction HS as [a HS IH]; intro HA.
      apply (candidate_neutral (CB a HA)); [now apply neutral_application|].
      intros u HU.
      destruct (neutral_application_reduction _ _ _ HN HU)
        as [[g [Hg ->]]|[b [Hb ->]]].
      * exact (proj2 (HF g Hg) a HA).
      * apply (proj2 (CS a b HA Hb _)).
        apply (IH b Hb). exact (candidate_reduct CA HA Hb).
Qed.

Lemma normalizing_lambda : forall b, strongly_normalizing b ->
  strongly_normalizing (TLam b).
Proof.
  intros b H; induction H as [b H IH]. constructor; intros u HU.
  inversion HU; subst; [discriminate|now apply IH].
Qed.
Lemma computations_substitute : forall b b', computation b b' -> forall a,
  rtc computation (subst a 0 b) (subst a 0 b').
Proof.
  intros b b' H a; apply pstep_computations, pstep_subst;
    [now apply computation_pstep|apply pstep_refl].
Qed.

Theorem dependent_lambda_from_normalizing_body : forall A B,
  candidate A -> (forall a, A a -> candidate (B a)) -> stable_family A B ->
  forall b, strongly_normalizing b ->
    (forall a, A a -> B a (subst a 0 b)) ->
    dependent_function A B (TLam b).
Proof.
  intros A B CA CB CS b HB.
  induction HB as [b HB IHb]; intro HF; split.
  - apply normalizing_lambda; constructor; exact HB.
  - intros a HA. pose proof (candidate_normalizing CA HA) as HS.
    revert HA; induction HS as [a HS IHa]; intro HA.
    apply (candidate_neutral (CB a HA)); [exact I|].
    intros u HU; inversion HU; subst.
    + cbn [root_step] in H; inversion H; subst. now apply HF.
    + match goal with HR : computation (TLam b) ?g |- _ =>
        inversion HR; subst; [discriminate|] end.
      assert (HF' : forall x, A x -> B x (subst x 0 b')).
      { intros x HX; eapply candidate_reducts;
          [apply CB; exact HX|apply computations_substitute; exact H0|apply HF; exact HX]. }
      exact (proj2 (IHb b' H0 HF') a HA).
    + match goal with HR : computation a ?a' |- _ =>
        apply (proj2 (CS a a' HA HR _)); apply (IHa a' HR);
          exact (candidate_reduct CA HA HR) end.
Qed.

Print Assumptions dependent_function_candidate.
Theorem dependent_lambda_computable : forall A B,
  candidate A -> (forall a, A a -> candidate (B a)) -> stable_family A B ->
  forall b, (forall a, A a -> B a (subst a 0 b)) ->
    dependent_function A B (TLam b).
Proof.
  intros A B CA CB CS b HF.
  eapply dependent_lambda_from_normalizing_body; try eassumption.
  pose proof (candidate_variable A CA 0) as Hvar.
  exact (substitution_reflects_normalization b (TVar 0) 0
    (candidate_normalizing (CB _ Hvar) (HF _ Hvar))).
Qed.
Print Assumptions dependent_lambda_computable.

Lemma neutral_fst_reduction : forall p u, neutral p -> computation (TFst p) u ->
  exists p', computation p p' /\ u = TFst p'.
Proof.
  intros p u HN HR; inversion HR; subst; eauto.
  destruct p; cbn [neutral root_step] in *; tauto || discriminate.
Qed.
Lemma neutral_snd_reduction : forall p u, neutral p -> computation (TSnd p) u ->
  exists p', computation p p' /\ u = TSnd p'.
Proof.
  intros p u HN HR; inversion HR; subst; eauto.
  destruct p; cbn [neutral root_step] in *; tauto || discriminate.
Qed.

Definition dependent_pair (A : term -> Prop) (B : term -> term -> Prop) p :=
  strongly_normalizing p /\ A (TFst p) /\ B (TFst p) (TSnd p).

Theorem dependent_pair_candidate : forall A B,
  candidate A -> (forall a, A a -> candidate (B a)) -> stable_family A B ->
  candidate (dependent_pair A B).
Proof.
  intros A B CA CB CS; constructor.
  - intros p [HS _]; exact HS.
  - intros p q [HS [HA HB]] HR. split; [exact (Acc_inv HS HR)|].
    assert (HA' : A (TFst q)) by
      (eapply candidate_reduct; [exact CA|exact HA|now apply cmp_TFst_p]).
    split; [exact HA'|].
    apply (proj1 (CS _ _ HA (cmp_TFst_p _ _ HR) _)).
    eapply candidate_reduct; [apply CB; exact HA|exact HB|now apply cmp_TSnd_p].
  - intros p HN HR. split.
    + constructor; intros u HU; exact (proj1 (HR u HU)).
    + assert (HA : A (TFst p)).
      { apply (candidate_neutral CA); [exact I|].
        intros u HU; destruct (neutral_fst_reduction _ _ HN HU) as [p' [Hp ->]].
        exact (proj1 (proj2 (HR p' Hp))). }
      split; [exact HA|].
      apply (candidate_neutral (CB _ HA)); [exact I|].
      intros u HU; destruct (neutral_snd_reduction _ _ HN HU) as [p' [Hp ->]].
      apply (proj2 (CS _ _ HA (cmp_TFst_p _ _ Hp) _)).
      exact (proj2 (proj2 (HR p' Hp))).
Qed.

Lemma normalizing_pair : forall a b,
  strongly_normalizing a -> strongly_normalizing b ->
  strongly_normalizing (TPair a b).
Proof.
  intros a b HA; revert b; induction HA as [a HA IHa]; intros b HB.
  induction HB as [b HB IHb]; constructor; intros u HU.
  inversion HU; subst; [discriminate| |].
  - apply IHa; [eassumption|constructor; exact HB].
  - apply IHb; eassumption.
Qed.

Lemma candidate_fst_pair : forall R, candidate R -> forall a b,
  R a -> strongly_normalizing b -> R (TFst (TPair a b)).
Proof.
  intros R CR a b HA HB.
  pose proof (normalizing_pair _ _ (candidate_normalizing CR HA) HB) as HS.
  clear HB; remember (TPair a b) as p eqn:HE; revert a b HE HA.
  induction HS as [p HS IH]; intros a b HE HA; subst p.
  apply (candidate_neutral CR); [exact I|].
  intros u HU; inversion HU; subst.
  - cbn [root_step] in H; inversion H; subst; exact HA.
  - match goal with HP : computation (TPair a b) _ |- _ =>
      inversion HP; subst; [discriminate| |] end.
    + eapply IH; [apply cmp_TPair_a; eassumption|reflexivity|].
      eapply candidate_reduct; eassumption.
    + eapply IH; [apply cmp_TPair_b; eassumption|reflexivity|exact HA].
Qed.
Lemma candidate_snd_pair : forall R, candidate R -> forall a b,
  strongly_normalizing a -> R b -> R (TSnd (TPair a b)).
Proof.
  intros R CR a b HA HB.
  pose proof (normalizing_pair _ _ HA (candidate_normalizing CR HB)) as HS.
  clear HA; remember (TPair a b) as p eqn:HE; revert a b HE HB.
  induction HS as [p HS IH]; intros a b HE HB; subst p.
  apply (candidate_neutral CR); [exact I|].
  intros u HU; inversion HU; subst.
  - cbn [root_step] in H; inversion H; subst; exact HB.
  - match goal with HP : computation (TPair a b) _ |- _ =>
      inversion HP; subst; [discriminate| |] end.
    + eapply IH; [apply cmp_TPair_a; eassumption|reflexivity|exact HB].
    + eapply IH; [apply cmp_TPair_b; eassumption|reflexivity|].
      eapply candidate_reduct; eassumption.
Qed.

Theorem dependent_pair_computable : forall A B,
  candidate A -> (forall a, A a -> candidate (B a)) -> stable_family A B ->
  forall a b, A a -> B a b -> dependent_pair A B (TPair a b).
Proof.
  intros A B CA CB CS a b HA HB.
  pose proof (candidate_normalizing CA HA) as HSA.
  pose proof (candidate_normalizing (CB _ HA) HB) as HSB.
  split; [now apply normalizing_pair|].
  pose proof (candidate_fst_pair _ CA _ _ HA HSB) as HF.
  split; [exact HF|].
  apply (proj2 (CS _ _ HF (cmp_root (TFst (TPair a b)) a eq_refl) _)).
  exact (candidate_snd_pair _ (CB _ HA) _ _ HSA HB).
Qed.

Print Assumptions dependent_pair_candidate.
Print Assumptions dependent_pair_computable.

Lemma normalizing_context_reflection : forall C,
  (forall t u, computation t u -> computation (C t) (C u)) ->
  forall t, strongly_normalizing (C t) -> strongly_normalizing t.
Proof.
  intros C HC t H; remember (C t) as s eqn:HE; revert t HE.
  induction H as [s H IH]; intros t HE; subst s.
  constructor; intros u HU; apply (IH (C u)); [now apply HC|reflexivity].
Qed.
Lemma normalizing_lift_reflection : forall t d c,
  strongly_normalizing (lift d c t) -> strongly_normalizing t.
Proof.
  intros t d c H; pose proof (accessible_apstep _ H) as HS; clear H.
  remember (lift d c t) as s eqn:HE; revert t HE.
  induction HS as [s HS IH]; intros t HE; subst s.
  constructor; intros u HU; apply (IH (lift d c u));
    [now apply apstep_lift, computation_apstep|reflexivity].
Qed.

Theorem dependent_function_eta : forall A B,
  candidate A -> (forall a, A a -> candidate (B a)) -> stable_family A B ->
  forall f, dependent_function A B (TLam (TApp (lift 1 0 f) (TVar 0))) <->
    dependent_function A B f.
Proof.
  intros A B CA CB CS f; split.
  - intros [HS HF]; split.
    + apply (normalizing_lift_reflection f 1 0).
      apply (normalizing_context_reflection (fun t => TApp t (TVar 0)));
        [intros; now apply cmp_TApp_f|].
      apply (normalizing_context_reflection TLam);
        [intros; now apply cmp_TLam_b|exact HS].
    + intros a HA; eapply candidate_reduct; [apply CB; exact HA|apply HF; exact HA|].
      apply cmp_root; cbn [root_step subst]. now rewrite subst_lift_zero, lift_zero_id.
  - intros [HS HF]; apply (dependent_lambda_computable A B CA CB CS).
    intros a HA; cbn [subst]; rewrite subst_lift_zero, lift_zero_id; now apply HF.
Qed.

Theorem dependent_function_variance : forall A B A' B',
  (forall a, A' a -> A a) ->
  (forall a t, A' a -> B a t -> B' a t) ->
  forall f, dependent_function A B f -> dependent_function A' B' f.
Proof.
  intros A B A' B' HA HB f [HS HF]; split; [exact HS|].
  intros a H; apply HB; [exact H|apply HF; now apply HA].
Qed.

Print Assumptions dependent_function_eta.
Print Assumptions dependent_function_variance.
