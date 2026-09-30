(* Reducibility candidates for full beta/eta reduction.
   These strengthen the computation-only foundations used by the transfer proof. *)
From Stdlib Require Import Bool Lia.
Require Export nameless.DBFullReductionStructure.

Module Full.
Definition strongly_normalizing := full_SN.
Definition neutral t :=
  match t with
  | TVar _ | TFst _ | TSnd _ | TSwitch _ _ _ _ _
  | TEPi _ _ _ | TInterp _ _ _ | TIAll _ _ _ _ _
  | TInd _ _ _ _ _ _ | THyps _ _ _ _ _ _
  | TCloseCase _ _ _ _ _ _ _ _ | TCloseInd _ _ _ _ _ _ _ => True
  | TApp (TMuI _ _) _ | TApp (TClose _ _ _) _ => False
  | TApp _ _ => True
  | _ => False
  end.
Record candidate (R : term -> Prop) : Prop := {
  candidate_normalizing : forall t, R t -> strongly_normalizing t;
  candidate_reduct : forall t u, R t -> reduction t u -> R u;
  candidate_neutral : forall t, neutral t ->
    (forall u, reduction t u -> R u) -> R t
}.
Arguments candidate_normalizing {R} _ {t} _.
Arguments candidate_reduct {R} _ {t u} _ _.
Arguments candidate_neutral {R} _ {t} _ _.

Lemma candidate_reducts : forall R, candidate R ->
  forall t u, rtc reduction t u -> R t -> R u.
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
Definition not_lambda t := match t with TLam _ => false | _ => true end.
Lemma neutral_not_lambda : forall t, neutral t -> not_lambda t = true.
Proof. destruct t; cbn [neutral not_lambda]; tauto. Qed.
Lemma neutral_application : forall f a, neutral f -> neutral (TApp f a).
Proof. destruct f; cbn [neutral]; tauto. Qed.
Lemma neutral_application_reduction : forall f a u, neutral f ->
  reduction (TApp f a) u ->
  (exists f', reduction f f' /\ u = TApp f' a) \/
  (exists a', reduction a a' /\ u = TApp f a').
Proof.
  intros f a u HN HR; inversion HR; subst; eauto.
  destruct f; cbn [neutral root_step] in *; tauto || discriminate.
Qed.

Definition dependent_function (A : term -> Prop) (B : term -> term -> Prop) f :=
  strongly_normalizing f /\ forall a, A a -> B a (TApp f a).
Definition stable_family (A : term -> Prop) (B : term -> term -> Prop) :=
  forall a a', A a -> reduction a a' -> forall t, B a t <-> B a' t.

Theorem dependent_function_candidate : forall A B,
  candidate A -> (forall a, A a -> candidate (B a)) -> stable_family A B ->
  candidate (dependent_function A B).
Proof.
  intros A B CA CB CS; constructor.
  - intros f [HN _]; exact HN.
  - intros f g [HN HF] HR; split; [exact (Acc_inv HN HR)|].
    intros a HA; eapply candidate_reduct; [apply CB; exact HA|apply HF; exact HA|].
    now apply red_TApp_f.
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
Proof. exact full_SN_lambda. Qed.
Lemma reductions_substitute : forall b b', reduction b b' -> forall a,
  rtc reduction (subst a 0 b) (subst a 0 b').
Proof. intros; apply rtc_one; now apply reduction_subst. Qed.

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
    + match goal with HR : reduction (TLam b) ?g |- _ =>
        inversion HR; subst; [discriminate| |] end.
      * specialize (HF a HA). now rewrite subst_eta_app in HF.
      * match goal with HR : reduction b ?b' |- _ =>
          let HF' := fresh "HF'" in
          assert (HF' : forall x, A x -> B x (subst x 0 b')) by
            (intros x HX; eapply candidate_reducts;
              [apply CB; exact HX|apply reductions_substitute; exact HR|apply HF; exact HX]);
          exact (proj2 (IHb b' HR HF') a HA)
        end.
    + match goal with HR : reduction a ?a' |- _ =>
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
  exact (full_SN_subst_reflection b (TVar 0) 0
    (candidate_normalizing (CB _ Hvar) (HF _ Hvar))).
Qed.
Print Assumptions dependent_lambda_computable.

Lemma neutral_fst_reduction : forall p u, neutral p -> reduction (TFst p) u ->
  exists p', reduction p p' /\ u = TFst p'.
Proof.
  intros p u HN HR; inversion HR; subst; eauto.
  destruct p; cbn [neutral root_step] in *; tauto || discriminate.
Qed.
Lemma neutral_snd_reduction : forall p u, neutral p -> reduction (TSnd p) u ->
  exists p', reduction p p' /\ u = TSnd p'.
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
      (eapply candidate_reduct; [exact CA|exact HA|now apply red_TFst_p]).
    split; [exact HA'|].
    apply (proj1 (CS _ _ HA (@red_TFst_p _ _ HR) _)).
    eapply candidate_reduct; [apply CB; exact HA|exact HB|now apply red_TSnd_p].
  - intros p HN HR. split.
    + constructor; intros u HU; exact (proj1 (HR u HU)).
    + assert (HA : A (TFst p)).
      { apply (candidate_neutral CA); [exact I|].
        intros u HU; destruct (neutral_fst_reduction _ _ HN HU) as [p' [Hp ->]].
        exact (proj1 (proj2 (HR p' Hp))). }
      split; [exact HA|].
      apply (candidate_neutral (CB _ HA)); [exact I|].
      intros u HU; destruct (neutral_snd_reduction _ _ HN HU) as [p' [Hp ->]].
      apply (proj2 (CS _ _ HA (@red_TFst_p _ _ Hp) _)).
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
  - match goal with HP : reduction (TPair a b) _ |- _ =>
      inversion HP; subst; [discriminate| |] end.
    + eapply IH; [apply red_TPair_a; eassumption|reflexivity|].
      eapply candidate_reduct; eassumption.
    + eapply IH; [apply red_TPair_b; eassumption|reflexivity|exact HA].
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
  - match goal with HP : reduction (TPair a b) _ |- _ =>
      inversion HP; subst; [discriminate| |] end.
    + eapply IH; [apply red_TPair_a; eassumption|reflexivity|exact HB].
    + eapply IH; [apply red_TPair_b; eassumption|reflexivity|].
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
  apply (proj2 (CS _ _ HF (@red_root (TFst (TPair a b)) a eq_refl) _)).
  exact (candidate_snd_pair _ (CB _ HA) _ _ HSA HB).
Qed.

Print Assumptions dependent_pair_candidate.
Print Assumptions dependent_pair_computable.

Lemma normalizing_context_reflection : forall C,
  (forall t u, reduction t u -> reduction (C t) (C u)) ->
  forall t, strongly_normalizing (C t) -> strongly_normalizing t.
Proof.
  intros C HC t H; remember (C t) as s eqn:HE; revert t HE.
  induction H as [s H IH]; intros t HE; subst s.
  constructor; intros u HU; apply (IH (C u)); [now apply HC|reflexivity].
Qed.
Lemma normalizing_lift_reflection : forall t d c,
  strongly_normalizing (lift d c t) -> strongly_normalizing t.
Proof. exact full_SN_lift_reflection. Qed.

Theorem dependent_function_eta : forall A B,
  candidate A -> (forall a, A a -> candidate (B a)) -> stable_family A B ->
  forall f, dependent_function A B (TLam (TApp (lift 1 0 f) (TVar 0))) <->
    dependent_function A B f.
Proof.
  intros A B CA CB CS f; split.
  - intros [HS HF]; split.
    + apply (normalizing_lift_reflection f 1 0).
      apply (normalizing_context_reflection (fun t => TApp t (TVar 0)));
        [intros; now apply red_TApp_f|].
      apply (normalizing_context_reflection TLam);
        [intros; now apply red_TLam_b|exact HS].
    + intros a HA; eapply candidate_reduct; [apply CB; exact HA|apply HF; exact HA|].
      apply red_root; cbn [root_step subst]. now rewrite subst_lift_zero, lift_zero_id.
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

Definition predicate_equiv (R S : term -> Prop) := forall t, R t <-> S t.
Lemma candidate_equiv : forall R S,
  candidate R -> predicate_equiv R S -> candidate S.
Proof.
  intros R S CR HE; constructor.
  - intros t HS; apply (candidate_normalizing CR); now apply HE.
  - intros t u HS HR; apply HE; eapply candidate_reduct;
      [exact CR|apply HE; exact HS|exact HR].
  - intros t HN HR; apply HE; apply (candidate_neutral CR HN).
    intros u HU; apply HE; now apply HR.
Qed.
Lemma dependent_function_equiv : forall A B A' B',
  predicate_equiv A A' ->
  (forall a, A a -> predicate_equiv (B a) (B' a)) ->
  predicate_equiv (dependent_function A B) (dependent_function A' B').
Proof.
  intros A B A' B' HA HB f; unfold dependent_function; split; intros [HS HF];
    split; [exact HS| |exact HS|]; intros a Ha.
  - assert (H : A a) by now apply HA. apply (HB a H); now apply HF.
  - apply (HB a Ha), HF, HA; exact Ha.
Qed.
Lemma dependent_pair_equiv : forall A B A' B',
  predicate_equiv A A' ->
  (forall a, A a -> predicate_equiv (B a) (B' a)) ->
  predicate_equiv (dependent_pair A B) (dependent_pair A' B').
Proof.
  intros A B A' B' HA HB p; unfold dependent_pair; split; intros [HS [HF HG]].
  - split; [exact HS|]; split; [now apply HA|now apply (HB _ HF)].
  - assert (H : A (TFst p)) by now apply HA.
    split; [exact HS|]; split; [exact H|now apply (HB _ H)].
Qed.
End Full.
