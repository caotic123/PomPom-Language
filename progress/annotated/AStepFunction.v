(* An executable annotated root computation, exactly matching
   [structural_root], and decidability of full annotated reduction. *)
From Stdlib Require Import List Arith Bool.
Require Export annotated.AFullPreservation.
Import ListNotations.

Definition aroot_step (t : term) : option term :=
  match t with
  | TApp _ _ (TLam _ _ b) a => Some (subst a 0 b)
  | TFst _ _ (TPair _ _ a _) => Some a
  | TSnd _ _ (TPair _ _ _ b) => Some b
  | TEPi _ TNilE _ => Some TUnitT
  | TEPi k (TConsE tag E) P =>
      Some (aproduct (aepi_head k tag E P) (TEPi k E (atail_motive k tag E P)))
  | TSwitch _ (TConsE _ _) _ (TPair _ _ p _) (TEZero _ _) => Some p
  | TSwitch k (TConsE tag E) P (TPair _ _ _ ps) (TESucc _ _ n) =>
      Some (TSwitch k E (atail_motive k tag E P) ps n)
  | TInterp IT (TIVar _ i) X => Some (afamily_app IT X i)
  | TInterp _ (TI1 _) _ => Some TUnitT
  | TInterp _ (TIBot _) _ => Some abot
  | TInterp IT (TIProd _ A B) X =>
      Some (aproduct (TInterp IT A X) (TInterp IT B X))
  | TInterp IT (TIPi _ A D) X => Some (TPi A (ainterp_binder IT A D X))
  | TInterp IT (TISig _ A D) X => Some (TSigma A (ainterp_binder IT A D X))
  | TInterp IT (TIChoice _ E D) X =>
      Some (TSigma (TEnumT E) (ainterp_binder_enum IT E D X))
  | TIAll IT (TIVar _ i) X x P => Some (amotive_app IT X P (atotal_pair IT X i x))
  | TIAll _ (TI1 _) _ TUnit _ => Some TUnitT
  | TIAll _ (TIBot _) _ _ _ => Some TUnitT
  | TIAll IT (TIProd _ A B) X (TPair _ _ a b) P =>
      Some (aproduct (TIAll IT A X a P) (TIAll IT B X b P))
  | TIAll IT (TIPi _ A D) X f P => Some (TPi A (aiall_binder IT A D X f P))
  | TIAll IT (TISig _ A D) X (TPair _ _ a x) P =>
      Some (TIAll IT (ainstantiate IT A D a) X x P)
  | TIAll IT (TIChoice _ E D) X (TPair _ _ e x) P =>
      Some (TIAll IT (ainstantiate_enum IT E D e) X x P)
  | THyps IT (TIVar _ i) X P h x => Some (arec_app IT X P h i x)
  | THyps _ (TI1 _) _ _ _ TUnit => Some TUnit
  | THyps _ (TIBot _) _ _ _ _ => Some TUnit
  | THyps IT (TIProd _ A B) X P h (TPair _ _ a b) =>
      Some (ahyps_prod_pair IT A B X P h a b)
  | THyps IT (TIPi _ A D) X P h f =>
      Some (TLam A (aiall_binder IT A D X f P) (ahyps_binder IT A D X P h f))
  | THyps IT (TISig _ A D) X P h (TPair _ _ a x) =>
      Some (THyps IT (ainstantiate IT A D a) X P h x)
  | THyps IT (TIChoice _ E D) X P h (TPair _ _ e x) =>
      Some (THyps IT (ainstantiate_enum IT E D e) X P h x)
  | TInd IT D P st i (TInMu _ _ _ xs) => Some (amu_ind_reduct IT D P st i xs)
  | TCloseCase k IT F G i Q b (TInClose _ _ _ _ xs) =>
      Some (TApp (apayload IT F G i) (aclose_case_codomain k IT F G i Q) b xs)
  | TCloseInd IT G P st F i (TInClose _ _ _ _ xs) =>
      Some (aclose_ind_reduct IT G P st F i xs)
  | _ => None
  end.

Theorem aroot_step_sound : forall t u, aroot_step t = Some u -> structural_root t u.
Proof.
  intros t u H; destruct t; cbn [aroot_step] in H; try discriminate;
    repeat match type of H with
    | match ?x with _ => _ end = Some _ => destruct x; try discriminate
    end; inversion H; subst; constructor.
Qed.

Theorem aroot_step_complete : forall t u, structural_root t u -> aroot_step t = Some u.
Proof. intros t u H; destruct H; reflexivity. Qed.

Definition anormal t := forall u, ~ reduction t u.

#[local] Hint Constructors compatible : acompat.

Theorem reduction_decidable : forall t, (exists u, reduction t u) \/ anormal t.
Proof.
  induction t.
  all: match goal with |- _ \/ anormal ?t0 =>
    destruct (aroot_step t0) as [r|] eqn:Hroot;
    [left; exists r; apply step_root, aroot_step_sound; exact Hroot|] end.
  all: repeat match goal with
    | IH : (exists u, reduction ?s u) \/ anormal ?s |- _ =>
        let u := fresh "u" in let Hu := fresh "Hu" in
        destruct IH as [[u Hu]|IH];
        [left; eexists; apply step_context; solve [eauto 2 with acompat]|]
    end.
  all: try (match goal with |- context [TLam ?A ?B ?b] =>
    destruct (eta_contract (TLam A B b)) as [r|] eqn:Heta;
    [left; exists r; apply step_eta, eta_contract_sound; exact Heta|] end).
  all: right; intros v Hv; inversion Hv as [? ? Hr|? ? He|? ? Hc]; subst;
    [apply aroot_step_complete in Hr; congruence
    |try (apply eta_contract_complete in He; congruence); inversion He
    |inversion Hc; subst; eauto].
  all: match goal with
    | IH : anormal ?s, H : structural_step ?s _ |- _ => exact (IH _ H)
    end.
Qed.

Print Assumptions aroot_step_sound.
Print Assumptions reduction_decidable.
