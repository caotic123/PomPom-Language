(* Reducibility infrastructure for computation normalization. *)
From Stdlib Require Import Bool Lia.
Require Export nameless.DBNormalization.

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

Theorem dependent_lambda_computable : forall A B,
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
      Show.
Abort.
