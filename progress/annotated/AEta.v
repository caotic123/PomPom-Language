(* General eta on annotated syntax: no value/neutral restriction and no
   typing-of-the-reduct premise. The lift includes every annotation. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AFreshness annotated.AErasure.
Require nameless.DBWeakening.

Inductive eta_root : term -> term -> Prop :=
| eta_contract_root : forall A B C D f,
    eta_root (TLam A B (TApp C D (lift 1 0 f) (TVar 0))) f.

Definition eta_contract (t : term) : option term :=
  match t with
  | TLam _ _ (TApp _ _ f (TVar 0)) =>
      if occurs 0 f then None else Some (subst TUnit 0 f)
  | _ => None
  end.

Theorem eta_contract_sound : forall t u,
  eta_contract t = Some u -> eta_root t u.
Proof.
  destruct t; intros u H; cbn [eta_contract] in H; try discriminate.
  destruct t3; cbn [eta_contract] in H; try discriminate.
  destruct t3_4; cbn [eta_contract] in H; try discriminate.
  destruct n; cbn [eta_contract] in H; try discriminate.
  destruct (occurs 0 t3_3) eqn:HF; [discriminate|].
  inversion H; subst u.
  rewrite <- (lift_lower t3_3 0 TUnit HF) at 1.
  constructor.
Qed.

Theorem eta_contract_complete : forall t u,
  eta_root t u -> eta_contract t = Some u.
Proof.
  intros t u H; destruct H; cbn [eta_contract].
  now rewrite occurs_lift, subst_lift_zero.
Qed.

Theorem eta_root_lift : forall t u, eta_root t u -> forall d c,
  eta_root (lift d c t) (lift d c u).
Proof.
  intros t u H d c; destruct H; cbn [lift].
  rewrite lift_lift_one_zero; constructor.
Qed.

Theorem eta_root_subst : forall t u, eta_root t u -> forall v c,
  eta_root (subst v c t) (subst v c u).
Proof.
  intros t u H v c; destruct H; cbn [subst].
  rewrite subst_lift_one_zero; constructor.
Qed.

Theorem eta_root_erasure : forall t u, eta_root t u ->
  nameless.DBCore.reduction (erase t) (erase u).
Proof.
  intros t u H; destruct H; cbn [erase]; rewrite erase_lift.
  apply nameless.DBCore.red_eta.
Qed.

(* Beta and projections are the first annotated root computations. Other
   primitive computations will be included before exposing the full relation. *)
Inductive structural_root : term -> term -> Prop :=
| root_beta : forall A B C D b a,
    structural_root (TApp A B (TLam C D b) a) (subst a 0 b)
| root_fst : forall A B C D a b,
    structural_root (TFst A B (TPair C D a b)) a
| root_snd : forall A B C D a b,
    structural_root (TSnd A B (TPair C D a b)) b.

Theorem structural_root_erasure : forall t u, structural_root t u ->
  nameless.DBCore.reduction (erase t) (erase u).
Proof.
  intros t u H; destruct H; cbn [erase];
    try rewrite erase_subst; apply nameless.DBCore.red_root; reflexivity.
Qed.

Definition conversion t u := nameless.DBCore.conv (erase t) (erase u).

Lemma compatible_erasure_conversion : forall R,
  (forall t u, R t u -> conversion t u) -> forall t u,
  compatible R t u -> conversion t u.
Proof.
  intros R HR t u H; destruct H; unfold conversion in *; cbn [erase];
    try solve [apply nameless.DBCore.cv_refl];
    apply nameless.DBCore.cv_compatible; constructor;
    auto using nameless.DBCore.cv_refl.
Qed.

Inductive structural_step : term -> term -> Prop :=
| step_root : forall t u, structural_root t u -> structural_step t u
| step_eta : forall t u, eta_root t u -> structural_step t u
| step_context : forall t u,
    compatible structural_step t u -> structural_step t u.

Lemma structural_step_conversion : forall t u,
  structural_step t u -> conversion t u.
Proof.
  fix IH 3; intros t u H; destruct H.
  - apply nameless.DBWeakening.reduction_conversion, structural_root_erasure; assumption.
  - apply nameless.DBWeakening.reduction_conversion, eta_root_erasure; assumption.
  - destruct H; unfold conversion; cbn [erase];
      try solve [apply nameless.DBCore.cv_refl];
      apply nameless.DBCore.cv_compatible; constructor;
      first [apply nameless.DBCore.cv_refl | apply IH; assumption].
Qed.

Print Assumptions eta_contract_sound.
Print Assumptions eta_root_subst.
Print Assumptions structural_step_conversion.
