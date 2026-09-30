From Stdlib Require Import List Arith Bool Lia String.
Require Export FullReductionStructureWork.

Definition term_eq_dec : forall t u : term, {t = u} + {t <> u}.
Proof. decide equality; apply String.string_dec || apply Nat.eq_dec. Defined.

Definition eta_contract t : option term :=
  match t with
  | TLam (TApp f (TVar 0)) =>
    let g := subst (TVar 0) 0 f in
    if term_eq_dec f (lift 1 0 g) then Some g else None
  | _ => None
  end.
Lemma eta_contract_sound : forall t u, eta_contract t = Some u -> reduction t u.
Proof.
  destruct t; intros u H; cbn [eta_contract] in H; try discriminate.
  destruct t; cbn [eta_contract] in H; try discriminate.
  destruct t2; cbn [eta_contract] in H; try discriminate.
  destruct n; cbn [eta_contract] in H; try discriminate.
  destruct (term_eq_dec t1 (lift 1 0 (subst (TVar 0) 0 t1))) as [HE|HE];
    [|discriminate].
  inversion H; subst u. rewrite HE at 1. apply red_eta.
Qed.
Lemma eta_contract_eta : forall f,
  eta_contract (TLam (TApp (lift 1 0 f) (TVar 0))) = Some f.
Proof.
  intros f; cbn [eta_contract]; rewrite subst_lift_zero.
  destruct (term_eq_dec (lift 1 0 f) (lift 1 0 f)); [reflexivity|contradiction].
Qed.
Definition head_next t :=
  match root_step t with Some u => Some u | None => eta_contract t end.
Lemma head_next_sound : forall t u, head_next t = Some u -> reduction t u.
Proof.
  intros t u H; unfold head_next in H; destruct (root_step t) eqn:HR.
  - inversion H; subst; now apply red_root.
  - now apply eta_contract_sound.
Qed.
Lemma head_next_no_root : forall t, head_next t = None -> root_step t = None.
Proof.
  intros t H; unfold head_next in H; destruct (root_step t); congruence.
Qed.
Lemma head_next_eta : forall f,
  head_next (TLam (TApp (lift 1 0 f) (TVar 0))) = Some f.
Proof. intros f; unfold head_next; cbn [root_step]; apply eta_contract_eta. Qed.

Fixpoint full_next (t : term) : option term :=
  match head_next t with
  | Some u => Some u
  | None => match t with
    | TVar n => None
    | TSort k => None
    | TPi A B => match full_next A with Some A' => Some (TPi A' B) | None => match full_next B with Some B' => Some (TPi A B') | None => None end end
    | TLam b => match full_next b with Some b' => Some (TLam b') | None => None end
    | TApp f a => match full_next f with Some f' => Some (TApp f' a) | None => match full_next a with Some a' => Some (TApp f a') | None => None end end
    | TSigma A B => match full_next A with Some A' => Some (TSigma A' B) | None => match full_next B with Some B' => Some (TSigma A B') | None => None end end
    | TPair a b => match full_next a with Some a' => Some (TPair a' b) | None => match full_next b with Some b' => Some (TPair a b') | None => None end end
    | TFst p => match full_next p with Some p' => Some (TFst p') | None => None end
    | TSnd p => match full_next p with Some p' => Some (TSnd p') | None => None end
    | TUnitT => None
    | TUnit => None
    | TUId => None
    | TTag s => None
    | TEnumU => None
    | TNilE => None
    | TConsE tag E => match full_next tag with Some tag' => Some (TConsE tag' E) | None => match full_next E with Some E' => Some (TConsE tag E') | None => None end end
    | TEnumT E => match full_next E with Some E' => Some (TEnumT E') | None => None end
    | TEZero => None
    | TESucc n => match full_next n with Some n' => Some (TESucc n') | None => None end
    | TEPi k E P => match full_next E with Some E' => Some (TEPi k E' P) | None => match full_next P with Some P' => Some (TEPi k E P') | None => None end end
    | TSwitch k E P p e => match full_next E with Some E' => Some (TSwitch k E' P p e) | None => match full_next P with Some P' => Some (TSwitch k E P' p e) | None => match full_next p with Some p' => Some (TSwitch k E P p' e) | None => match full_next e with Some e' => Some (TSwitch k E P p e') | None => None end end end end
    | TIDesc IT => match full_next IT with Some IT' => Some (TIDesc IT') | None => None end
    | TIVar i => match full_next i with Some i' => Some (TIVar i') | None => None end
    | TI1 => None
    | TIBot => None
    | TIProd A B => match full_next A with Some A' => Some (TIProd A' B) | None => match full_next B with Some B' => Some (TIProd A B') | None => None end end
    | TIPi A D => match full_next A with Some A' => Some (TIPi A' D) | None => match full_next D with Some D' => Some (TIPi A D') | None => None end end
    | TISig A D => match full_next A with Some A' => Some (TISig A' D) | None => match full_next D with Some D' => Some (TISig A D') | None => None end end
    | TIChoice E D => match full_next E with Some E' => Some (TIChoice E' D) | None => match full_next D with Some D' => Some (TIChoice E D') | None => None end end
    | TInterp IT D X => match full_next IT with Some IT' => Some (TInterp IT' D X) | None => match full_next D with Some D' => Some (TInterp IT D' X) | None => match full_next X with Some X' => Some (TInterp IT D X') | None => None end end end
    | TMuI IT D => match full_next IT with Some IT' => Some (TMuI IT' D) | None => match full_next D with Some D' => Some (TMuI IT D') | None => None end end
    | TIn x => match full_next x with Some x' => Some (TIn x') | None => None end
    | TInd IT D P s i x => match full_next IT with Some IT' => Some (TInd IT' D P s i x) | None => match full_next D with Some D' => Some (TInd IT D' P s i x) | None => match full_next P with Some P' => Some (TInd IT D P' s i x) | None => match full_next s with Some s' => Some (TInd IT D P s' i x) | None => match full_next i with Some i' => Some (TInd IT D P s i' x) | None => match full_next x with Some x' => Some (TInd IT D P s i x') | None => None end end end end end end
    | TIAll IT D X x P => match full_next IT with Some IT' => Some (TIAll IT' D X x P) | None => match full_next D with Some D' => Some (TIAll IT D' X x P) | None => match full_next X with Some X' => Some (TIAll IT D X' x P) | None => match full_next x with Some x' => Some (TIAll IT D X x' P) | None => match full_next P with Some P' => Some (TIAll IT D X x P') | None => None end end end end end
    | THyps IT D X P h x => match full_next IT with Some IT' => Some (THyps IT' D X P h x) | None => match full_next D with Some D' => Some (THyps IT D' X P h x) | None => match full_next X with Some X' => Some (THyps IT D X' P h x) | None => match full_next P with Some P' => Some (THyps IT D X P' h x) | None => match full_next h with Some h' => Some (THyps IT D X P h' x) | None => match full_next x with Some x' => Some (THyps IT D X P h x') | None => None end end end end end end
    | TClose IT F G => match full_next IT with Some IT' => Some (TClose IT' F G) | None => match full_next F with Some F' => Some (TClose IT F' G) | None => match full_next G with Some G' => Some (TClose IT F G') | None => None end end end
    | TCloseCase k IT F G i Q b x => match full_next IT with Some IT' => Some (TCloseCase k IT' F G i Q b x) | None => match full_next F with Some F' => Some (TCloseCase k IT F' G i Q b x) | None => match full_next G with Some G' => Some (TCloseCase k IT F G' i Q b x) | None => match full_next i with Some i' => Some (TCloseCase k IT F G i' Q b x) | None => match full_next Q with Some Q' => Some (TCloseCase k IT F G i Q' b x) | None => match full_next b with Some b' => Some (TCloseCase k IT F G i Q b' x) | None => match full_next x with Some x' => Some (TCloseCase k IT F G i Q b x') | None => None end end end end end end end
    | TCloseInd IT G P s F i x => match full_next IT with Some IT' => Some (TCloseInd IT' G P s F i x) | None => match full_next G with Some G' => Some (TCloseInd IT G' P s F i x) | None => match full_next P with Some P' => Some (TCloseInd IT G P' s F i x) | None => match full_next s with Some s' => Some (TCloseInd IT G P s' F i x) | None => match full_next F with Some F' => Some (TCloseInd IT G P s F' i x) | None => match full_next i with Some i' => Some (TCloseInd IT G P s F i' x) | None => match full_next x with Some x' => Some (TCloseInd IT G P s F i x') | None => None end end end end end end end
    end
  end.

Lemma full_next_sound : forall t u, full_next t = Some u -> reduction t u.
Proof.
  induction t; intros u H; cbn [full_next] in H.
  all: match type of H with context [match head_next ?s with _ => _ end] =>
    destruct (head_next s) eqn:HR end.
  all: try solve [inversion H; subst; now apply head_next_sound].
  all: repeat match type of H with context [match full_next ?s with _ => _ end] =>
    destruct (full_next s) eqn:? end.
  all: try discriminate; inversion H; subst; solve [constructor; auto].
Qed.
Lemma full_next_complete : forall t,
  full_next t = None -> forall u, ~ reduction t u.
Proof.
  induction t; intros HN u Hu; cbn [full_next] in HN.
  all: match type of HN with context [match head_next ?s with _ => _ end] =>
    destruct (head_next s) eqn:HH; [discriminate|] end.
  all: repeat match type of HN with context [match full_next ?s with _ => _ end] =>
    destruct (full_next s) eqn:?; [discriminate|] end.
  all: pose proof (head_next_no_root _ HH) as Hroot.
  all: inversion Hu; subst; try congruence.
  all: try solve [match goal with
    IH : _ = _ -> forall u, ~ reduction ?t u,
    HR : reduction ?t ?u |- _ => exact (IH eq_refl u HR) end].
  rewrite head_next_eta in HH; discriminate.
Qed.
Definition normal_form t := forall u, ~ reduction t u.

Definition normalize_full : forall t, full_SN t ->
  {u : term | rtc reduction t u /\ normal_form u}.
Proof.
  intros t H; induction H as [t H IH].
  destruct (full_next t) as [u|] eqn:HN.
  - destruct (IH u (full_next_sound _ _ HN)) as [v [HR HV]].
    exists v; split; [eapply rtc_step; [exact (full_next_sound _ _ HN)|exact HR]|exact HV].
  - exists t; split; [apply rtc_refl|exact (full_next_complete t HN)].
Defined.
Lemma normal_reductions_identity : forall t u,
  normal_form t -> rtc reduction t u -> t = u.
Proof. intros t u HN HR; inversion HR; [reflexivity|exfalso; eapply HN; eassumption]. Qed.
Lemma normal_conversion_unique : forall t u,
  normal_form t -> normal_form u -> conv t u -> t = u.
Proof.
  intros t u HT HU HC; destruct (conversion_joinable _ _ HC) as [w [Ht Hu]].
  pose proof (normal_reductions_identity _ _ HT Ht).
  pose proof (normal_reductions_identity _ _ HU Hu). congruence.
Qed.
Lemma normal_form_accessible : forall t, normal_form t -> full_SN t.
Proof. intros t H; constructor; intros u HU; exfalso; exact (H u HU). Qed.
Lemma full_SN_reductions : forall t, full_SN t ->
  forall u, rtc reduction t u -> full_SN u.
Proof.
  intros t H u HR; induction HR; [exact H|].
  apply IHHR; exact (Acc_inv H H0).
Qed.
Lemma normal_forms_join : forall t u A B,
  conv t u -> rtc reduction t A -> rtc reduction u B ->
  normal_form A -> normal_form B -> A = B.
Proof.
  intros t u A B HC HA HB HNA HNB. apply normal_conversion_unique; try assumption.
  eapply cv_trans; [apply cv_sym; exact (reductions_conversion _ _ HA)|].
  eapply cv_trans; [exact HC|exact (reductions_conversion _ _ HB)].
Qed.

Print Assumptions normalize_full.
Print Assumptions normal_forms_join.

Section BinaryNormalForms.
Variable C : term -> term -> term.
Hypothesis C_reduction : forall a b u, reduction (C a b) u ->
  (exists a', reduction a a' /\ u = C a' b) \/
  (exists b', reduction b b' /\ u = C a b').
Lemma full_SN_binary : forall a b, full_SN a -> full_SN b -> full_SN (C a b).
Proof.
  intros a b HA; revert b; induction HA as [a HA IHa]; intros b HB.
  induction HB as [b HB IHb]; constructor; intros u HU.
  destruct (C_reduction _ _ _ HU) as [[a' [Ha ->]]|[b' [Hb ->]]].
  - apply IHa; [exact Ha|constructor; exact HB].
  - now apply IHb.
Qed.
Lemma normal_form_binary : forall a b,
  normal_form a -> normal_form b -> normal_form (C a b).
Proof.
  intros a b HA HB u HU.
  destruct (C_reduction _ _ _ HU) as [[a' [Ha ->]]|[b' [Hb ->]]];
    [exact (HA _ Ha)|exact (HB _ Hb)].
Qed.
End BinaryNormalForms.
Lemma pi_reduction_components : forall a b u, reduction (TPi a b) u ->
  (exists a', reduction a a' /\ u = TPi a' b) \/
  (exists b', reduction b b' /\ u = TPi a b').
Proof. intros a b u H; inversion H; subst; cbn [root_step] in *; try discriminate; eauto. Qed.
Lemma sigma_reduction_components : forall a b u, reduction (TSigma a b) u ->
  (exists a', reduction a a' /\ u = TSigma a' b) \/
  (exists b', reduction b b' /\ u = TSigma a b').
Proof. intros a b u H; inversion H; subst; cbn [root_step] in *; try discriminate; eauto. Qed.
Lemma full_SN_pi : forall a b, full_SN a -> full_SN b -> full_SN (TPi a b).
Proof. exact (full_SN_binary TPi pi_reduction_components). Qed.
Lemma full_SN_sigma : forall a b, full_SN a -> full_SN b -> full_SN (TSigma a b).
Proof. exact (full_SN_binary TSigma sigma_reduction_components). Qed.
Lemma normal_form_pi : forall a b,
  normal_form a -> normal_form b -> normal_form (TPi a b).
Proof. exact (normal_form_binary TPi pi_reduction_components). Qed.
Lemma normal_form_sigma : forall a b,
  normal_form a -> normal_form b -> normal_form (TSigma a b).
Proof. exact (normal_form_binary TSigma sigma_reduction_components). Qed.
Lemma reductions_subst : forall t u, rtc reduction t u -> forall a c,
  rtc reduction (subst a c t) (subst a c u).
Proof. intros t u H a c; induction H; [apply rtc_refl|eapply rtc_step; [exact (reduction_subst _ _ H a c)|exact IHrtc]]. Qed.
