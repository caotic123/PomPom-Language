(* Shape facts needed for eta preservation and typed postponement. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBRootPreservation.

Definition function_head (t : term) : bool :=
  match t with
  | TVar _ | TLam _ | TApp _ _ | TFst _ | TSnd _
  | TSwitch _ _ _ _ _ | TMuI _ _ | TInd _ _ _ _ _ _
  | THyps _ _ _ _ _ _ | TClose _ _ _
  | TCloseCase _ _ _ _ _ _ _ _ | TCloseInd _ _ _ _ _ _ _ => true
  | _ => false
  end.

Lemma typing_function_head : forall Gamma t T, typing Gamma t T ->
  forall A B, conv T (TPi A B) -> function_head t = true.
Proof.
  intros Gamma t T H; induction H; intros AA BB HC;
    cbn [function_head]; try reflexivity.
  all: try solve [exfalso;
    pose proof (conversion_head _ _ _ _ HC eq_refl eq_refl); discriminate].
  - eapply IHtyping1; eapply cv_trans; eassumption.
  - eapply IHtyping1; apply cv_refl.
Qed.

Lemma application_function_generation : forall Gamma t T,
  typing Gamma t T -> forall f a, t = TApp f a ->
  exists A B, typing Gamma f (TPi A B).
Proof.
  intros Gamma t T H; induction H; intros fn arg HE; try discriminate; eauto.
  inversion HE; subst; eauto.
Qed.

Lemma function_head_lift : forall t d c,
  function_head (lift d c t) = function_head t.
Proof. destruct t; intros; cbn [lift function_head]; try reflexivity.
  destruct (n <? c); reflexivity. Qed.

Theorem eta_reduct_function_head : forall Gamma f T,
  typing Gamma (TLam (TApp (lift 1 0 f) (TVar 0))) T ->
  function_head f = true.
Proof.
  intros Gamma f T H.
  destruct (lambda_generation _ _ _ H _ eq_refl)
    as [A [B [k [HP [Hb HC]]]]].
  destruct (application_function_generation _ _ _ Hb _ _ eq_refl)
    as [C [D Hf]].
  pose proof (typing_function_head _ _ _ Hf _ _ (cv_refl _)) as HF.
  now rewrite function_head_lift in HF.
Qed.

Print Assumptions eta_reduct_function_head.
