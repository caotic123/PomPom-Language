(* Helpers for confluence modulo annotations: compositional raw freshness,
   remaining generation lemmas, rigid-head separation of types, and the
   correspondence between raw root redexes of an erasure and annotated
   redexes. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.ACfRaw annotated.ACompleteness.
Import ListNotations.

(* ---- compositional raw freshness ---- *)
Lemma rf_TVar : forall x n, n <> x -> raw_fresh x (Raw.TVar n).
Proof.
  intros x n Hn; destruct (Nat.ltb_spec n x).
  - exists (Raw.TVar n); cbn [Raw.lift]; destruct (Nat.ltb_spec n x); [reflexivity|lia].
  - exists (Raw.TVar (Nat.pred n)); cbn [Raw.lift].
    destruct (Nat.ltb_spec (Nat.pred n) x); [lia|f_equal; lia].
Qed.
Lemma rf_TSort : forall cut k, raw_fresh cut (Raw.TSort k).
Proof. intros; exists (Raw.TSort k); reflexivity. Qed.
Lemma rf_TPi : forall cut A B, raw_fresh cut A -> raw_fresh (S cut) B ->
  raw_fresh cut (Raw.TPi A B).
Proof. intros cut A B [A0 ->] [B0 ->]; exists (Raw.TPi A0 B0); reflexivity. Qed.
Lemma rf_TLam : forall cut b, raw_fresh (S cut) b ->
  raw_fresh cut (Raw.TLam b).
Proof. intros cut b [b0 ->]; exists (Raw.TLam b0); reflexivity. Qed.
Lemma rf_TApp : forall cut f a, raw_fresh cut f -> raw_fresh cut a ->
  raw_fresh cut (Raw.TApp f a).
Proof. intros cut f a [f0 ->] [a0 ->]; exists (Raw.TApp f0 a0); reflexivity. Qed.
Lemma rf_TSigma : forall cut A B, raw_fresh cut A -> raw_fresh (S cut) B ->
  raw_fresh cut (Raw.TSigma A B).
Proof. intros cut A B [A0 ->] [B0 ->]; exists (Raw.TSigma A0 B0); reflexivity. Qed.
Lemma rf_TPair : forall cut a b, raw_fresh cut a -> raw_fresh cut b ->
  raw_fresh cut (Raw.TPair a b).
Proof. intros cut a b [a0 ->] [b0 ->]; exists (Raw.TPair a0 b0); reflexivity. Qed.
Lemma rf_TFst : forall cut p, raw_fresh cut p ->
  raw_fresh cut (Raw.TFst p).
Proof. intros cut p [p0 ->]; exists (Raw.TFst p0); reflexivity. Qed.
Lemma rf_TSnd : forall cut p, raw_fresh cut p ->
  raw_fresh cut (Raw.TSnd p).
Proof. intros cut p [p0 ->]; exists (Raw.TSnd p0); reflexivity. Qed.
Lemma rf_TUnitT : forall cut, raw_fresh cut (Raw.TUnitT).
Proof. intros; exists (Raw.TUnitT); reflexivity. Qed.
Lemma rf_TUnit : forall cut, raw_fresh cut (Raw.TUnit).
Proof. intros; exists (Raw.TUnit); reflexivity. Qed.
Lemma rf_TUId : forall cut, raw_fresh cut (Raw.TUId).
Proof. intros; exists (Raw.TUId); reflexivity. Qed.
Lemma rf_TTag : forall cut s, raw_fresh cut (Raw.TTag s).
Proof. intros; exists (Raw.TTag s); reflexivity. Qed.
Lemma rf_TEnumU : forall cut, raw_fresh cut (Raw.TEnumU).
Proof. intros; exists (Raw.TEnumU); reflexivity. Qed.
Lemma rf_TNilE : forall cut, raw_fresh cut (Raw.TNilE).
Proof. intros; exists (Raw.TNilE); reflexivity. Qed.
Lemma rf_TConsE : forall cut tag E, raw_fresh cut tag -> raw_fresh cut E ->
  raw_fresh cut (Raw.TConsE tag E).
Proof. intros cut tag E [tag0 ->] [E0 ->]; exists (Raw.TConsE tag0 E0); reflexivity. Qed.
Lemma rf_TEnumT : forall cut E, raw_fresh cut E ->
  raw_fresh cut (Raw.TEnumT E).
Proof. intros cut E [E0 ->]; exists (Raw.TEnumT E0); reflexivity. Qed.
Lemma rf_TEZero : forall cut, raw_fresh cut (Raw.TEZero).
Proof. intros; exists (Raw.TEZero); reflexivity. Qed.
Lemma rf_TESucc : forall cut n, raw_fresh cut n ->
  raw_fresh cut (Raw.TESucc n).
Proof. intros cut n [n0 ->]; exists (Raw.TESucc n0); reflexivity. Qed.
Lemma rf_TEPi : forall cut k E P, raw_fresh cut E -> raw_fresh cut P ->
  raw_fresh cut (Raw.TEPi k E P).
Proof. intros cut k E P [E0 ->] [P0 ->]; exists (Raw.TEPi k E0 P0); reflexivity. Qed.
Lemma rf_TSwitch : forall cut k E P p e, raw_fresh cut E -> raw_fresh cut P -> raw_fresh cut p -> raw_fresh cut e ->
  raw_fresh cut (Raw.TSwitch k E P p e).
Proof. intros cut k E P p e [E0 ->] [P0 ->] [p0 ->] [e0 ->]; exists (Raw.TSwitch k E0 P0 p0 e0); reflexivity. Qed.
Lemma rf_TIDesc : forall cut IT, raw_fresh cut IT ->
  raw_fresh cut (Raw.TIDesc IT).
Proof. intros cut IT [IT0 ->]; exists (Raw.TIDesc IT0); reflexivity. Qed.
Lemma rf_TIVar : forall cut i, raw_fresh cut i ->
  raw_fresh cut (Raw.TIVar i).
Proof. intros cut i [i0 ->]; exists (Raw.TIVar i0); reflexivity. Qed.
Lemma rf_TI1 : forall cut, raw_fresh cut (Raw.TI1).
Proof. intros; exists (Raw.TI1); reflexivity. Qed.
Lemma rf_TIBot : forall cut, raw_fresh cut (Raw.TIBot).
Proof. intros; exists (Raw.TIBot); reflexivity. Qed.
Lemma rf_TIProd : forall cut A B, raw_fresh cut A -> raw_fresh cut B ->
  raw_fresh cut (Raw.TIProd A B).
Proof. intros cut A B [A0 ->] [B0 ->]; exists (Raw.TIProd A0 B0); reflexivity. Qed.
Lemma rf_TIPi : forall cut A D, raw_fresh cut A -> raw_fresh cut D ->
  raw_fresh cut (Raw.TIPi A D).
Proof. intros cut A D [A0 ->] [D0 ->]; exists (Raw.TIPi A0 D0); reflexivity. Qed.
Lemma rf_TISig : forall cut A D, raw_fresh cut A -> raw_fresh cut D ->
  raw_fresh cut (Raw.TISig A D).
Proof. intros cut A D [A0 ->] [D0 ->]; exists (Raw.TISig A0 D0); reflexivity. Qed.
Lemma rf_TIChoice : forall cut E D, raw_fresh cut E -> raw_fresh cut D ->
  raw_fresh cut (Raw.TIChoice E D).
Proof. intros cut E D [E0 ->] [D0 ->]; exists (Raw.TIChoice E0 D0); reflexivity. Qed.
Lemma rf_TInterp : forall cut IT D X, raw_fresh cut IT -> raw_fresh cut D -> raw_fresh cut X ->
  raw_fresh cut (Raw.TInterp IT D X).
Proof. intros cut IT D X [IT0 ->] [D0 ->] [X0 ->]; exists (Raw.TInterp IT0 D0 X0); reflexivity. Qed.
Lemma rf_TMuI : forall cut IT D, raw_fresh cut IT -> raw_fresh cut D ->
  raw_fresh cut (Raw.TMuI IT D).
Proof. intros cut IT D [IT0 ->] [D0 ->]; exists (Raw.TMuI IT0 D0); reflexivity. Qed.
Lemma rf_TIn : forall cut x, raw_fresh cut x ->
  raw_fresh cut (Raw.TIn x).
Proof. intros cut x [x0 ->]; exists (Raw.TIn x0); reflexivity. Qed.
Lemma rf_TInd : forall cut IT D P s i x, raw_fresh cut IT -> raw_fresh cut D -> raw_fresh cut P -> raw_fresh cut s -> raw_fresh cut i -> raw_fresh cut x ->
  raw_fresh cut (Raw.TInd IT D P s i x).
Proof. intros cut IT D P s i x [IT0 ->] [D0 ->] [P0 ->] [s0 ->] [i0 ->] [x0 ->]; exists (Raw.TInd IT0 D0 P0 s0 i0 x0); reflexivity. Qed.
Lemma rf_TIAll : forall cut IT D X x P, raw_fresh cut IT -> raw_fresh cut D -> raw_fresh cut X -> raw_fresh cut x -> raw_fresh cut P ->
  raw_fresh cut (Raw.TIAll IT D X x P).
Proof. intros cut IT D X x P [IT0 ->] [D0 ->] [X0 ->] [x0 ->] [P0 ->]; exists (Raw.TIAll IT0 D0 X0 x0 P0); reflexivity. Qed.
Lemma rf_THyps : forall cut IT D X P h x, raw_fresh cut IT -> raw_fresh cut D -> raw_fresh cut X -> raw_fresh cut P -> raw_fresh cut h -> raw_fresh cut x ->
  raw_fresh cut (Raw.THyps IT D X P h x).
Proof. intros cut IT D X P h x [IT0 ->] [D0 ->] [X0 ->] [P0 ->] [h0 ->] [x0 ->]; exists (Raw.THyps IT0 D0 X0 P0 h0 x0); reflexivity. Qed.
Lemma rf_TClose : forall cut IT F G, raw_fresh cut IT -> raw_fresh cut F -> raw_fresh cut G ->
  raw_fresh cut (Raw.TClose IT F G).
Proof. intros cut IT F G [IT0 ->] [F0 ->] [G0 ->]; exists (Raw.TClose IT0 F0 G0); reflexivity. Qed.
Lemma rf_TCloseCase : forall cut k IT F G i Q b x, raw_fresh cut IT -> raw_fresh cut F -> raw_fresh cut G -> raw_fresh cut i -> raw_fresh cut Q -> raw_fresh cut b -> raw_fresh cut x ->
  raw_fresh cut (Raw.TCloseCase k IT F G i Q b x).
Proof. intros cut k IT F G i Q b x [IT0 ->] [F0 ->] [G0 ->] [i0 ->] [Q0 ->] [b0 ->] [x0 ->]; exists (Raw.TCloseCase k IT0 F0 G0 i0 Q0 b0 x0); reflexivity. Qed.
Lemma rf_TCloseInd : forall cut IT G P s F i x, raw_fresh cut IT -> raw_fresh cut G -> raw_fresh cut P -> raw_fresh cut s -> raw_fresh cut F -> raw_fresh cut i -> raw_fresh cut x ->
  raw_fresh cut (Raw.TCloseInd IT G P s F i x).
Proof. intros cut IT G P s F i x [IT0 ->] [G0 ->] [P0 ->] [s0 ->] [F0 ->] [i0 ->] [x0 ->]; exists (Raw.TCloseInd IT0 G0 P0 s0 F0 i0 x0); reflexivity. Qed.

Lemma rf_lift1 : forall x A, raw_fresh x A -> raw_fresh (S x) (Raw.lift 1 0 A).
Proof. exact raw_fresh_shift. Qed.
Lemma rf_liftd : forall d x A, raw_fresh x A -> raw_fresh (d + x) (Raw.lift d 0 A).
Proof.
  intros d x A [A0 ->]; exists (Raw.lift d 0 A0).
  pose proof (RB.lift_lift_comm A0 1 d 0 x (Nat.le_0_l x)) as H.
  symmetry; exact H.
Qed.
Lemma rf_lift2 : forall x A, raw_fresh x A -> raw_fresh (S (S x)) (Raw.lift 2 0 A).
Proof. intros; exact (rf_liftd 2 x A H). Qed.
Lemma rf_lift3 : forall x A, raw_fresh x A -> raw_fresh (S (S (S x))) (Raw.lift 3 0 A).
Proof. intros; exact (rf_liftd 3 x A H). Qed.
Lemma rf_lift4 : forall x A, raw_fresh x A -> raw_fresh (S (S (S (S x)))) (Raw.lift 4 0 A).
Proof. intros; exact (rf_liftd 4 x A H). Qed.
Lemma rf_var_under : forall x n, n < S x -> raw_fresh (S x) (Raw.TVar n).
Proof. intros; apply rf_TVar; lia. Qed.

Create HintDb rfresh.
#[export] Hint Resolve rf_TSort rf_TPi rf_TLam rf_TApp rf_TSigma rf_TPair rf_TFst
  rf_TSnd rf_TUnitT rf_TUnit rf_TUId rf_TTag rf_TEnumU rf_TNilE rf_TConsE rf_TEnumT
  rf_TEZero rf_TESucc rf_TEPi rf_TSwitch rf_TIDesc rf_TIVar rf_TI1 rf_TIBot
  rf_TIProd rf_TIPi rf_TISig rf_TIChoice rf_TInterp rf_TMuI rf_TIn rf_TInd
  rf_TIAll rf_THyps rf_TClose rf_TCloseCase rf_TCloseInd rf_lift1 rf_lift2
  rf_lift3 rf_lift4 raw_fresh_subst : rfresh.
#[export] Hint Extern 1 (raw_fresh _ (Raw.TVar _)) => apply rf_TVar; lia : rfresh.

Ltac unfold_raw_macros :=
  unfold Raw.arrow, Raw.product, Raw.Def, Raw.Family, Raw.Bot, Raw.CloseAt,
    Raw.MuAt, Raw.carrier, Raw.payload, Raw.total, Raw.motive,
    Raw.recursive_method, Raw.close_case_method, Raw.close_motive,
    Raw.diagonal_motive, Raw.close_ind_method, Raw.mu_ind_method in *.
Ltac rfresh_step := first
  [ assumption | (apply rf_TVar; lia) | apply rf_TSort | apply rf_TPi | apply rf_TLam | apply rf_TApp | apply rf_TSigma | apply rf_TPair | apply rf_TFst | apply rf_TSnd | apply rf_TUnitT | apply rf_TUnit | apply rf_TUId | apply rf_TTag | apply rf_TEnumU | apply rf_TNilE | apply rf_TConsE | apply rf_TEnumT | apply rf_TEZero | apply rf_TESucc | apply rf_TEPi | apply rf_TSwitch | apply rf_TIDesc | apply rf_TIVar | apply rf_TI1 | apply rf_TIBot | apply rf_TIProd | apply rf_TIPi | apply rf_TISig | apply rf_TIChoice | apply rf_TInterp | apply rf_TMuI | apply rf_TIn | apply rf_TInd | apply rf_TIAll | apply rf_THyps | apply rf_TClose | apply rf_TCloseCase | apply rf_TCloseInd
  | apply rf_lift1 | apply rf_lift2 | apply rf_lift3 | apply rf_lift4
  | apply raw_fresh_subst ].
Ltac rfresh := unfold_raw_macros; repeat rfresh_step.

(* ---- annotated freshness ---- *)
Lemma occurs_fresh_erase : forall x t, occurs x t = false -> raw_fresh x (erase t).
Proof.
  intros x t H; apply occurs_false_iff_lift in H; destruct H as [t0 ->].
  exists (erase t0); apply erase_lift.
Qed.

Definition ctx_fresh (Delta : Raw.ctx) x :=
  forall y A, y < x -> nth_error Delta y = Some A -> raw_fresh x (Raw.lift (S y) 0 A).

Lemma ctx_fresh_extend : forall Delta x A, ctx_fresh Delta x -> raw_fresh x A ->
  ctx_fresh (A :: Delta) (S x).
Proof.
  intros Delta x A HD HA [|y] B Hy HB; cbn [nth_error] in HB.
  - inversion HB; subst; exact (rf_lift1 _ _ HA).
  - assert (Hf : raw_fresh x (Raw.lift (S y) 0 B)) by (apply HD; [lia|exact HB]).
    pose proof (rf_lift1 _ _ Hf) as H1.
    pose proof (RB.lift_fuse B 1 (S y) 0 0 (Nat.le_0_l _)) as HE; cbn in HE.
    rewrite HE in H1; exact H1.
Qed.

Lemma ctx_fresh_zero : forall Delta, ctx_fresh Delta 0.
Proof. intros Delta y A Hy; lia. Qed.

(* ---- remaining generation lemmas ---- *)
Definition shape_TVar t := match t with TVar _ => True | _ => False end.
Definition shape_TSort t := match t with TSort _ => True | _ => False end.
Definition shape_TFst t := match t with TFst _ _ _ => True | _ => False end.
Definition shape_TSnd t := match t with TSnd _ _ _ => True | _ => False end.
Definition shape_TEnumT t := match t with TEnumT _ => True | _ => False end.
Definition shape_TIDesc t := match t with TIDesc _ => True | _ => False end.

Lemma var_generation : forall Gamma t T, typing Gamma t T ->
  shape_TVar t -> exists n A, t = TVar n /\ nth_error Gamma n = Some A /\
  RC.type_comparison (Raw.lift (S n) 0 A) T.
Proof. agen. Qed.

Lemma sort_generation : forall Gamma t T, typing Gamma t T ->
  shape_TSort t -> exists k, t = TSort k /\ RC.type_comparison (Raw.TSort (S k)) T.
Proof. agen. Qed.

Lemma fst_generation : forall Gamma t T, typing Gamma t T ->
  shape_TFst t -> exists A B p j k, t = TFst A B p /\
  typing Gamma A (Raw.TSort j) /\ typing (erase A :: Gamma) B (Raw.TSort k) /\
  typing Gamma p (Raw.TSigma (erase A) (erase B)) /\
  RC.type_comparison (erase A) T.
Proof. agen. Qed.

Lemma snd_generation : forall Gamma t T, typing Gamma t T ->
  shape_TSnd t -> exists A B p j k, t = TSnd A B p /\
  typing Gamma A (Raw.TSort j) /\ typing (erase A :: Gamma) B (Raw.TSort k) /\
  typing Gamma p (Raw.TSigma (erase A) (erase B)) /\
  RC.type_comparison (Raw.subst (Raw.TFst (erase p)) 0 (erase B)) T.
Proof. agen. Qed.

Lemma enumt_generation : forall Gamma t T, typing Gamma t T ->
  shape_TEnumT t -> exists E, t = TEnumT E /\ typing Gamma E Raw.TEnumU /\
  RC.type_comparison (Raw.TSort 0) T.
Proof. agen. Qed.

Lemma idesc_generation : forall Gamma t T, typing Gamma t T ->
  shape_TIDesc t -> exists IT, t = TIDesc IT /\ typing Gamma IT (Raw.TSort 0) /\
  RC.type_comparison (Raw.TSort 1) T.
Proof. agen. Qed.

(* Constants: the principal type is fixed. *)
Definition const_type t := match t with
  | TUnitT | TUId | TEnumU => Some (Raw.TSort 0)
  | TUnit => Some Raw.TUnitT
  | TTag _ => Some Raw.TUId
  | TNilE => Some Raw.TEnumU
  | _ => None
  end.

Lemma constant_generation : forall Gamma t T, typing Gamma t T ->
  forall P, const_type t = Some P -> RC.type_comparison P T.
Proof.
  intros Gamma t T H; induction H; intros P0 HP; cbn in HP; try discriminate;
    try (inversion HP; subst; apply RC.cmp_conversion, RCore.cv_refl).
  - eapply RC.comparison_right_conversion; [apply IHtyping; exact HP|eassumption].
  - eapply RC.comparison_transitive; [apply IHtyping; exact HP|].
    apply RC.comparison_universe, RT.ul_sort; assumption.
  - eapply RC.comparison_transitive; [apply IHtyping; exact HP|].
    apply RC.comparison_universe, RT.ul_pi; assumption.
Qed.

(* ---- rigid heads ---- *)
Lemma cmp_rigid_conv : forall P T h, RC.type_comparison P T ->
  RG.term_head P = Some h -> h <> RG.h_pi -> h <> RG.h_sort -> RCore.conv P T.
Proof.
  intros P T h H HP Hpi Hsort; inversion H; subst; auto.
  - pose proof (RG.conversion_head _ _ _ _ H0 HP eq_refl); congruence.
  - pose proof (RG.conversion_head _ _ _ _ H0 HP eq_refl); congruence.
Qed.

Lemma cmp_not_pi : forall P T h X Y, RC.type_comparison P T ->
  RCore.conv T (Raw.TPi X Y) -> RG.term_head P = Some h -> h <> RG.h_pi -> False.
Proof.
  intros P T h X Y H HT HP Hpi; inversion H; subst.
  - pose proof (RG.conversion_head _ _ _ _ (RCore.cv_trans H0 HT) HP eq_refl); congruence.
  - pose proof (RG.conversion_head _ _ _ _ (RCore.cv_trans (RCore.cv_sym H1) HT) eq_refl eq_refl); discriminate.
  - pose proof (RG.conversion_head _ _ _ _ H0 HP eq_refl); congruence.
Qed.

Lemma cmp_not_sigma : forall P T h X Y, RC.type_comparison P T ->
  RCore.conv T (Raw.TSigma X Y) -> RG.term_head P = Some h -> h <> RG.h_sigma -> False.
Proof.
  intros P T h X Y H HT HP Hs; inversion H; subst.
  - pose proof (RG.conversion_head _ _ _ _ (RCore.cv_trans H0 HT) HP eq_refl); congruence.
  - pose proof (RG.conversion_head _ _ _ _ (RCore.cv_trans (RCore.cv_sym H1) HT) eq_refl eq_refl); discriminate.
  - pose proof (RG.conversion_head _ _ _ _ (RCore.cv_trans (RCore.cv_sym H1) HT) eq_refl eq_refl); discriminate.
Qed.

Definition elim_form t := match t with
  | TVar _ | TApp _ _ _ _ | TFst _ _ _ | TSnd _ _ _ | TSwitch _ _ _ _ _
  | TEPi _ _ _ | TInterp _ _ _ | TIAll _ _ _ _ _ | TInd _ _ _ _ _ _
  | THyps _ _ _ _ _ _ | TCloseCase _ _ _ _ _ _ _ _ | TCloseInd _ _ _ _ _ _ _
  | TMuI _ _ | TClose _ _ _ => True
  | _ => False
  end.

Ltac exclude_head :=
  match goal with
  | HC : RC.type_comparison ?P ?T, HT : RCore.conv ?T (Raw.TPi _ _) |- False =>
      eapply (cmp_not_pi P T); [exact HC|exact HT|reflexivity|discriminate]
  | HC : RC.type_comparison ?P ?T, HT : RCore.conv ?T (Raw.TSigma _ _) |- False =>
      eapply (cmp_not_sigma P T); [exact HC|exact HT|reflexivity|discriminate]
  end.

Ltac generate_shape H :=
  match type of H with
  | typing _ (TPi _ _) _ => destruct (pi_generation _ _ _ H I) as (?&?&?&?&?&?&?&?)
  | typing _ (TSigma _ _) _ => destruct (sigma_generation _ _ _ H I) as (?&?&?&?&?&?&?&?)
  | typing _ (TLam _ _ _) _ => destruct (lambda_generation _ _ _ H _ _ _ eq_refl) as (?&?&?&?&?&?)
  | typing _ (TPair _ _ _ _) _ => destruct (pair_generation _ _ _ H _ _ _ _ eq_refl) as (?&?&?&?&?&?&?)
  | typing _ (TSort _) _ => destruct (sort_generation _ _ _ H I) as (?&?&?)
  | typing _ (TEnumT _) _ => destruct (enumt_generation _ _ _ H I) as (?&?&?&?)
  | typing _ (TIDesc _) _ => destruct (idesc_generation _ _ _ H I) as (?&?&?&?)
  | typing _ (TConsE _ _) _ => destruct (conse_generation _ _ _ H I) as (?&?&?&?&?&?)
  | typing _ (TEZero _ _) _ => destruct (zero_generation _ _ _ H I) as (?&?&?&?&?&?)
  | typing _ (TESucc _ _ _) _ => destruct (succ_generation _ _ _ H I) as (?&?&?&?&?&?&?&?)
  | typing _ (TIVar _ _) _ => destruct (ivar_generation _ _ _ H I) as (?&?&?&?&?&?)
  | typing _ (TI1 _) _ => destruct (i1_generation _ _ _ H I) as (?&?&?&?)
  | typing _ (TIBot _) _ => destruct (ibot_generation _ _ _ H I) as (?&?&?&?)
  | typing _ (TIProd _ _ _) _ => destruct (iprod_generation _ _ _ H I) as (?&?&?&?&?&?&?&?)
  | typing _ (TIPi _ _ _) _ => destruct (ipi_generation _ _ _ H I) as (?&?&?&?&?&?&?&?)
  | typing _ (TISig _ _ _) _ => destruct (isig_generation _ _ _ H I) as (?&?&?&?&?&?&?&?)
  | typing _ (TIChoice _ _ _) _ => destruct (ichoice_generation _ _ _ H I) as (?&?&?&?&?&?&?&?)
  | typing _ (TInMu _ _ _ _) _ => destruct (in_mui_generation _ _ _ H I) as (?&?&?&?&?&?&?&?&?&?)
  | typing _ (TInClose _ _ _ _ _) _ => destruct (in_close_generation _ _ _ H I) as (?&?&?&?&?&?&?&?&?&?&?&?)
  end.

Lemma pi_typed_shape : forall Delta g T X Y, typing Delta g T ->
  RCore.conv T (Raw.TPi X Y) -> (exists A B b, g = TLam A B b) \/ elim_form g.
Proof.
  intros Delta g T X Y H HT; destruct g; try (right; exact I);
    try (left; eauto; fail); exfalso.
  all: try (pose proof (constant_generation _ _ _ H _ eq_refl) as HC; exclude_head).
  all: generate_shape H; subst; exclude_head.
Qed.

Lemma sigma_typed_shape : forall Delta p T X Y, typing Delta p T ->
  RCore.conv T (Raw.TSigma X Y) -> (exists A B a b, p = TPair A B a b) \/ elim_form p.
Proof.
  intros Delta p T X Y H HT; destruct p; try (right; exact I);
    try (left; eauto; fail); exfalso.
  all: try (pose proof (constant_generation _ _ _ H _ eq_refl) as HC; exclude_head).
  all: generate_shape H; subst; exclude_head.
Qed.

(* ---- raw root redexes of an erasure ---- *)
Definition in_mismatch t := match t with
  | TInd _ _ _ _ _ (TInClose _ _ _ _ _) => True
  | TCloseCase _ _ _ _ _ _ _ (TInMu _ _ _ _) => True
  | TCloseInd _ _ _ _ _ _ (TInMu _ _ _ _) => True
  | _ => False
  end.

Lemma root_erasure_redex : forall t s, RCore.root_step (erase t) = Some s ->
  (exists u, aroot_step t = Some u) \/ in_mismatch t.
Proof.
  intros t s H; destruct t; cbn [erase RCore.root_step] in H; try discriminate.
  all: repeat match type of H with
    | context [match erase ?x with _ => _ end] => destruct x; cbn [erase] in H; try discriminate
    end.
  all: first [left; eexists; reflexivity | right; exact I].
Qed.

Lemma mismatch_untyped : forall Delta t T, typing Delta t T -> in_mismatch t -> False.
Proof.
  intros Delta t T H HM; destruct t; try contradiction.
  - destruct t6; try contradiction.
    destruct (ind_generation _ _ _ H I) as (?&?&?&?&?&?&HE&?&?&?&?&?&Hx&?); inversion HE; subst.
    destruct (in_close_generation _ _ _ Hx I) as (?&?&?&?&?&HE'&?&?&?&?&?&HC); inversion HE'; subst.
    pose proof (cmp_rigid_conv _ _ _ HC eq_refl ltac:(discriminate) ltac:(discriminate)) as HV.
    pose proof (RG.conversion_head _ _ _ _ HV eq_refl eq_refl); discriminate.
  - destruct t7; try contradiction.
    destruct (close_case_generation _ _ _ H I) as (?&?&?&?&?&?&?&?&HE&?&?&?&?&?&?&Hx&?); inversion HE; subst.
    destruct (in_mui_generation _ _ _ Hx I) as (?&?&?&?&HE'&?&?&?&?&HC); inversion HE'; subst.
    pose proof (cmp_rigid_conv _ _ _ HC eq_refl ltac:(discriminate) ltac:(discriminate)) as HV.
    pose proof (RG.conversion_head _ _ _ _ HV eq_refl eq_refl); discriminate.
  - destruct t7; try contradiction.
    destruct (close_ind_generation _ _ _ H I) as (?&?&?&?&?&?&?&HE&?&?&?&?&?&?&Hx&?); inversion HE; subst.
    destruct (in_mui_generation _ _ _ Hx I) as (?&?&?&?&HE'&?&?&?&?&HC); inversion HE'; subst.
    pose proof (cmp_rigid_conv _ _ _ HC eq_refl ltac:(discriminate) ltac:(discriminate)) as HV.
    pose proof (RG.conversion_head _ _ _ _ HV eq_refl eq_refl); discriminate.
Qed.

Lemma typed_normal_no_root : forall Delta t T s, typing Delta t T -> anormal t ->
  RCore.root_step (erase t) = Some s -> False.
Proof.
  intros Delta t T s HT HN HR.
  destruct (root_erasure_redex _ _ HR) as [[u Hu]|HM].
  - exact (HN u (step_root _ _ (aroot_step_sound _ _ Hu))).
  - exact (mismatch_untyped _ _ _ HT HM).
Qed.

#[export] Hint Constructors compatible : acompat.
Ltac subnormal :=
  match goal with
  | H : anormal ?t |- anormal ?s =>
      let u := fresh "u" in let Hu := fresh "Hu" in
      intros u Hu; eapply H; apply step_context; solve [eauto 2 with acompat]
  end.

Print Assumptions pi_typed_shape.
Print Assumptions typed_normal_no_root.
