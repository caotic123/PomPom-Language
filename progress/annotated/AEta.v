(* General eta on annotated syntax: no value/neutral restriction and no
   typing-of-the-reduct premise. The lift includes every annotation. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.AFreshness annotated.AErasure.
Require Export annotated.AMacros.
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

(* All annotated primitive root computations, mirroring the raw [root_step]
   clauses. Reducts use the annotated macros from AMacros so that erasure
   lands syntactically on the raw reducts. *)
Inductive structural_root : term -> term -> Prop :=
| root_beta : forall A B C D b a,
    structural_root (TApp A B (TLam C D b) a) (subst a 0 b)
| root_fst : forall A B C D a b,
    structural_root (TFst A B (TPair C D a b)) a
| root_snd : forall A B C D a b,
    structural_root (TSnd A B (TPair C D a b)) b
| root_epi_nil : forall k P,
    structural_root (TEPi k TNilE P) TUnitT
| root_epi_cons : forall k tag E P,
    structural_root (TEPi k (TConsE tag E) P)
      (aproduct (aepi_head k tag E P) (TEPi k E (atail_motive k tag E P)))
| root_switch_zero : forall k tag E P A B p ps t' E',
    structural_root
      (TSwitch k (TConsE tag E) P (TPair A B p ps) (TEZero t' E')) p
| root_switch_succ : forall k tag E P A B p ps t' E' n,
    structural_root
      (TSwitch k (TConsE tag E) P (TPair A B p ps) (TESucc t' E' n))
      (TSwitch k E (atail_motive k tag E P) ps n)
| root_interp_var : forall IT IT' i X,
    structural_root (TInterp IT (TIVar IT' i) X) (afamily_app IT X i)
| root_interp_1 : forall IT IT' X,
    structural_root (TInterp IT (TI1 IT') X) TUnitT
| root_interp_bot : forall IT IT' X,
    structural_root (TInterp IT (TIBot IT') X) abot
| root_interp_prod : forall IT IT' A B X,
    structural_root (TInterp IT (TIProd IT' A B) X)
      (aproduct (TInterp IT A X) (TInterp IT B X))
| root_interp_pi : forall IT IT' A D X,
    structural_root (TInterp IT (TIPi IT' A D) X)
      (TPi A (ainterp_binder IT A D X))
| root_interp_sig : forall IT IT' A D X,
    structural_root (TInterp IT (TISig IT' A D) X)
      (TSigma A (ainterp_binder IT A D X))
| root_interp_choice : forall IT IT' E D X,
    structural_root (TInterp IT (TIChoice IT' E D) X)
      (TSigma (TEnumT E) (ainterp_binder_enum IT E D X))
| root_iall_var : forall IT IT' i X x P,
    structural_root (TIAll IT (TIVar IT' i) X x P)
      (amotive_app IT X P (atotal_pair IT X i x))
| root_iall_1 : forall IT IT' X P,
    structural_root (TIAll IT (TI1 IT') X TUnit P) TUnitT
| root_iall_bot : forall IT IT' X x P,
    structural_root (TIAll IT (TIBot IT') X x P) TUnitT
| root_iall_prod : forall IT IT' A B X A' B' a b P,
    structural_root (TIAll IT (TIProd IT' A B) X (TPair A' B' a b) P)
      (aproduct (TIAll IT A X a P) (TIAll IT B X b P))
| root_iall_pi : forall IT IT' A D X f P,
    structural_root (TIAll IT (TIPi IT' A D) X f P)
      (TPi A (aiall_binder IT A D X f P))
| root_iall_sig : forall IT IT' A D X A' B' a x P,
    structural_root (TIAll IT (TISig IT' A D) X (TPair A' B' a x) P)
      (TIAll IT (ainstantiate IT A D a) X x P)
| root_iall_choice : forall IT IT' E D X A' B' e x P,
    structural_root (TIAll IT (TIChoice IT' E D) X (TPair A' B' e x) P)
      (TIAll IT (ainstantiate_enum IT E D e) X x P)
| root_hyps_var : forall IT IT' i X P h x,
    structural_root (THyps IT (TIVar IT' i) X P h x) (arec_app IT X P h i x)
| root_hyps_1 : forall IT IT' X P h,
    structural_root (THyps IT (TI1 IT') X P h TUnit) TUnit
| root_hyps_bot : forall IT IT' X P h x,
    structural_root (THyps IT (TIBot IT') X P h x) TUnit
| root_hyps_prod : forall IT IT' A B X P h A' B' a b,
    structural_root (THyps IT (TIProd IT' A B) X P h (TPair A' B' a b))
      (ahyps_prod_pair IT A B X P h a b)
| root_hyps_pi : forall IT IT' A D X P h f,
    structural_root (THyps IT (TIPi IT' A D) X P h f)
      (TLam A (aiall_binder IT A D X f P) (ahyps_binder IT A D X P h f))
| root_hyps_sig : forall IT IT' A D X P h A' B' a x,
    structural_root (THyps IT (TISig IT' A D) X P h (TPair A' B' a x))
      (THyps IT (ainstantiate IT A D a) X P h x)
| root_hyps_choice : forall IT IT' E D X P h A' B' e x,
    structural_root (THyps IT (TIChoice IT' E D) X P h (TPair A' B' e x))
      (THyps IT (ainstantiate_enum IT E D e) X P h x)
| root_ind : forall IT D P st i IT' D' i' xs,
    structural_root (TInd IT D P st i (TInMu IT' D' i' xs))
      (amu_ind_reduct IT D P st i xs)
| root_close_case : forall k IT F G i Q b IT' F' G' i' xs,
    structural_root (TCloseCase k IT F G i Q b (TInClose IT' F' G' i' xs))
      (TApp (apayload IT F G i) (aclose_case_codomain k IT F G i Q) b xs)
| root_close_ind : forall IT G P st F i IT' F' G' i' xs,
    structural_root (TCloseInd IT G P st F i (TInClose IT' F' G' i' xs))
      (aclose_ind_reduct IT G P st F i xs).

Ltac aroot_norm :=
  cbn [erase lift subst aproduct abot aarrow aepi_head atail_motive
    afamily_app adef_app aCloseAt aMuAt acarrier apayload aDef atotal amotive
    arec_pair arec_codomain arecursive_method adesc_app_binder
    adesc_app_binder_enum ainterp_binder ainterp_binder_enum aapp_binder
    aiall_binder ahyps_binder ahyps_prod_pair ainstantiate
    ainstantiate_enum amu_rec_body amu_rec_lam adiagonal_motive
    aclose_rec_body aclose_rec_lam amu_payload amu_iall amu_result
    amu_ind_codomain amu_ind_method amethod_app acim_payload acim_iall
    acim_result acim_rest acim_method acmethod_app aclose_case_codomain
    atotal_pair amotive_app arec_app ahyps_mu amu_ind_reduct ahyps_close
    aclose_ind_reduct];
  repeat progress
    (cbn [erase]; repeat rewrite erase_lift; repeat rewrite erase_subst).

Theorem structural_root_erasure : forall t u, structural_root t u ->
  nameless.DBCore.reduction (erase t) (erase u).
Proof.
  intros t u H; destruct H; aroot_norm;
    apply nameless.DBCore.red_root; reflexivity.
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
