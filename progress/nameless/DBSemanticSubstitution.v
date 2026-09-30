(* Simultaneous substitution for semantic environments. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBSemanticVariance.
Import Full.

Fixpoint instantiate (rho : nat -> term) (cutoff : nat) (t : term) : term :=
  match t with
  | TVar n => if n <? cutoff then TVar n else lift cutoff 0 (rho (n - cutoff))
  | TSort k => TSort k
  | TPi A B => TPi (instantiate rho cutoff A) (instantiate rho (S cutoff) B)
  | TLam b => TLam (instantiate rho (S cutoff) b)
  | TApp f a => TApp (instantiate rho cutoff f) (instantiate rho cutoff a)
  | TSigma A B => TSigma (instantiate rho cutoff A) (instantiate rho (S cutoff) B)
  | TPair a b => TPair (instantiate rho cutoff a) (instantiate rho cutoff b)
  | TFst p => TFst (instantiate rho cutoff p)
  | TSnd p => TSnd (instantiate rho cutoff p)
  | TUnitT => TUnitT
  | TUnit => TUnit
  | TUId => TUId
  | TTag s => TTag s
  | TEnumU => TEnumU
  | TNilE => TNilE
  | TConsE tag E => TConsE (instantiate rho cutoff tag) (instantiate rho cutoff E)
  | TEnumT E => TEnumT (instantiate rho cutoff E)
  | TEZero => TEZero
  | TESucc n => TESucc (instantiate rho cutoff n)
  | TEPi k E P => TEPi k (instantiate rho cutoff E) (instantiate rho cutoff P)
  | TSwitch k E P p e => TSwitch k (instantiate rho cutoff E) (instantiate rho cutoff P) (instantiate rho cutoff p) (instantiate rho cutoff e)
  | TIDesc IT => TIDesc (instantiate rho cutoff IT)
  | TIVar i => TIVar (instantiate rho cutoff i)
  | TI1 => TI1
  | TIBot => TIBot
  | TIProd A B => TIProd (instantiate rho cutoff A) (instantiate rho cutoff B)
  | TIPi A D => TIPi (instantiate rho cutoff A) (instantiate rho cutoff D)
  | TISig A D => TISig (instantiate rho cutoff A) (instantiate rho cutoff D)
  | TIChoice E D => TIChoice (instantiate rho cutoff E) (instantiate rho cutoff D)
  | TInterp IT D X => TInterp (instantiate rho cutoff IT) (instantiate rho cutoff D) (instantiate rho cutoff X)
  | TMuI IT D => TMuI (instantiate rho cutoff IT) (instantiate rho cutoff D)
  | TIn x => TIn (instantiate rho cutoff x)
  | TInd IT D P s i x => TInd (instantiate rho cutoff IT) (instantiate rho cutoff D) (instantiate rho cutoff P) (instantiate rho cutoff s) (instantiate rho cutoff i) (instantiate rho cutoff x)
  | TIAll IT D X x P => TIAll (instantiate rho cutoff IT) (instantiate rho cutoff D) (instantiate rho cutoff X) (instantiate rho cutoff x) (instantiate rho cutoff P)
  | THyps IT D X P h x => THyps (instantiate rho cutoff IT) (instantiate rho cutoff D) (instantiate rho cutoff X) (instantiate rho cutoff P) (instantiate rho cutoff h) (instantiate rho cutoff x)
  | TClose IT F G => TClose (instantiate rho cutoff IT) (instantiate rho cutoff F) (instantiate rho cutoff G)
  | TCloseCase k IT F G i Q b x => TCloseCase k (instantiate rho cutoff IT) (instantiate rho cutoff F) (instantiate rho cutoff G) (instantiate rho cutoff i) (instantiate rho cutoff Q) (instantiate rho cutoff b) (instantiate rho cutoff x)
  | TCloseInd IT G P s F i x => TCloseInd (instantiate rho cutoff IT) (instantiate rho cutoff G) (instantiate rho cutoff P) (instantiate rho cutoff s) (instantiate rho cutoff F) (instantiate rho cutoff i) (instantiate rho cutoff x)
  end.

Definition extend_substitution a (rho : nat -> term) n :=
  match n with 0 => a | S k => rho k end.

Lemma instantiate_extension_var : forall rho a k n,
  subst a k (instantiate rho (S k) (TVar n)) =
  instantiate (extend_substitution a rho) k (TVar n).
Proof.
  intros rho a k n; cbn [instantiate].
  destruct (Nat.lt_trichotomy n k) as [HL|[->|HG]].
  - rewrite (proj2 (Nat.ltb_lt n (S k)) ltac:(lia)), (proj2 (Nat.ltb_lt n k) HL).
    cbn [subst]; now rewrite (proj2 (Nat.ltb_lt _ _) HL).
  - rewrite Nat.ltb_irrefl, (proj2 (Nat.ltb_lt k (S k)) ltac:(lia)), Nat.sub_diag.
    cbn [subst extend_substitution]; now rewrite Nat.ltb_irrefl, Nat.eqb_refl.
  - rewrite (proj2 (Nat.ltb_ge n (S k)) ltac:(lia)), (proj2 (Nat.ltb_ge n k) ltac:(lia)).
    rewrite subst_lift_prefix by lia.
    replace (n - k) with (S (n - S k)) by lia; reflexivity.
Qed.
Theorem instantiate_extension : forall t rho a k,
  subst a k (instantiate rho (S k) t) = instantiate (extend_substitution a rho) k t.
Proof.
  induction t; intros rho arg cutoff; cbn [instantiate subst];
    try solve [exact (instantiate_extension_var rho arg cutoff n)];
    f_equal; auto.
Qed.
Lemma instantiate_cons_lift_var : forall rho a k n,
  instantiate (extend_substitution a rho) k (lift 1 k (TVar n)) = instantiate rho k (TVar n).
Proof.
  intros rho a k n; cbn [lift instantiate].
  destruct (n <? k) eqn:HN.
  - cbn [instantiate]; now rewrite HN.
  - apply Nat.ltb_ge in HN; cbn [instantiate].
    rewrite (proj2 (Nat.ltb_ge (1+n) k) ltac:(lia)).
    replace (1 + n - k) with (S (n-k)) by lia; reflexivity.
Qed.
Theorem instantiate_cons_lift : forall t rho a k,
  instantiate (extend_substitution a rho) k (lift 1 k t) = instantiate rho k t.
Proof.
  induction t; intros rho arg cutoff; cbn [instantiate lift];
    try solve [exact (instantiate_cons_lift_var rho arg cutoff n)]; f_equal; auto.
Qed.
Lemma instantiate_lift_var : forall rho n d c k, c <= k ->
  instantiate rho (d+k) (lift d c (TVar n)) = lift d c (instantiate rho k (TVar n)).
Proof.
  intros rho n d c k Hck; cbn [lift instantiate].
  destruct (n <? c) eqn:HC; destruct (n <? k) eqn:HK;
    first [apply Nat.ltb_lt in HC|apply Nat.ltb_ge in HC];
    first [apply Nat.ltb_lt in HK|apply Nat.ltb_ge in HK]; try lia.
  - cbn [instantiate lift]; rewrite (proj2 (Nat.ltb_lt n (d+k)) ltac:(lia)), (proj2 (Nat.ltb_lt n c) HC); reflexivity.
  - cbn [instantiate lift]; rewrite (proj2 (Nat.ltb_lt (d+n) (d+k)) ltac:(lia)), (proj2 (Nat.ltb_ge n c) HC); reflexivity.
  - cbn [instantiate]; rewrite (proj2 (Nat.ltb_ge (d+n) (d+k)) ltac:(lia)).
    replace (d+n-(d+k)) with (n-k) by lia.
    symmetry; apply lift_fuse_zero; exact Hck.
Qed.
Theorem instantiate_lift : forall t rho d c k, c <= k ->
  instantiate rho (d+k) (lift d c t) = lift d c (instantiate rho k t).
Proof.
  induction t; intros rho amount pos depth Hck; cbn [instantiate lift];
    try solve [exact (instantiate_lift_var rho n amount pos depth Hck)];
    f_equal; try solve [auto];
    replace (S (amount+depth)) with (amount+S depth) by lia; apply IHt || apply IHt2; lia.
Qed.

Lemma instantiate_subst_var : forall rho u n c k, c <= k ->
  instantiate rho k (subst u c (TVar n)) =
  subst (instantiate rho (k-c) u) c (instantiate rho (S k) (TVar n)).
Proof.
  intros rho u n c k Hck; cbn [subst instantiate].
  destruct (Nat.lt_trichotomy n c) as [HL|[->|HG]].
  - rewrite (proj2 (Nat.ltb_lt n c) HL), (proj2 (Nat.ltb_lt n (S k)) ltac:(lia)).
    cbn [instantiate subst].
    now rewrite (proj2 (Nat.ltb_lt n k) ltac:(lia)), (proj2 (Nat.ltb_lt n c) HL).
  - rewrite Nat.ltb_irrefl, Nat.eqb_refl, (proj2 (Nat.ltb_lt c (S k)) ltac:(lia)).
    cbn [subst]; rewrite Nat.ltb_irrefl, Nat.eqb_refl.
    replace k with (c+(k-c)) at 1 by lia.
    apply instantiate_lift; lia.
  - rewrite (proj2 (Nat.ltb_ge n c) ltac:(lia)), (proj2 (Nat.eqb_neq n c) ltac:(lia)).
    destruct (n <? S k) eqn:HN.
    + apply Nat.ltb_lt in HN; cbn [instantiate subst].
      rewrite (proj2 (Nat.ltb_lt (Nat.pred n) k) ltac:(lia)).
      now rewrite (proj2 (Nat.ltb_ge n c) ltac:(lia)), (proj2 (Nat.eqb_neq n c) ltac:(lia)).
    + apply Nat.ltb_ge in HN; cbn [instantiate].
      rewrite (proj2 (Nat.ltb_ge (Nat.pred n) k) ltac:(lia)).
      rewrite subst_lift_prefix by lia.
      replace (Nat.pred n-k) with (n-S k) by lia; reflexivity.
Qed.
Theorem instantiate_subst : forall t rho u c k, c <= k ->
  instantiate rho k (subst u c t) =
  subst (instantiate rho (k-c) u) c (instantiate rho (S k) t).
Proof.
  induction t; intros rho arg pos depth Hpd; cbn [instantiate subst];
    try solve [exact (instantiate_subst_var rho arg n pos depth Hpd)];
    f_equal; try solve [auto].
  all: try (exact (IHt rho arg (S pos) (S depth) ltac:(lia))).
  all: try (exact (IHt2 rho arg (S pos) (S depth) ltac:(lia))).
Qed.
Corollary instantiate_subst_zero : forall t rho u,
  instantiate rho 0 (subst u 0 t) = subst (instantiate rho 0 u) 0 (instantiate rho 1 t).
Proof. intros; apply instantiate_subst; lia. Qed.

Print Assumptions instantiate_extension.
Print Assumptions instantiate_lift.
Print Assumptions instantiate_subst.

Lemma instantiate_lift_one : forall t rho k,
  instantiate rho (S k) (lift 1 0 t) = lift 1 0 (instantiate rho k t).
Proof. intros; exact (instantiate_lift t rho 1 0 k ltac:(lia)). Qed.
Lemma instantiate_lift_two : forall t rho k,
  instantiate rho (S (S k)) (lift 2 0 t) = lift 2 0 (instantiate rho k t).
Proof. intros; exact (instantiate_lift t rho 2 0 k ltac:(lia)). Qed.

Lemma instantiate_root_step : forall t u, root_step t = Some u -> forall rho k,
  root_step (instantiate rho k t) = Some (instantiate rho k u).
Proof.
  intros t u H; destruct t; cbn [root_step] in H; try discriminate;
    repeat match goal with H : match ?x with _ => _ end = Some _ |- _ =>
      destruct x; try discriminate end;
    inversion H; subst; intros rho depth;
    unfold product, Bot, carrier, diagonal_motive;
    repeat progress (cbn [instantiate root_step product Bot carrier diagonal_motive];
      rewrite ?instantiate_subst, ?instantiate_lift_one, ?instantiate_lift_two, ?Nat.sub_0_r by lia);
    reflexivity.
Qed.
Theorem reduction_instantiate : forall t u, reduction t u -> forall rho k,
  reduction (instantiate rho k t) (instantiate rho k u).
Proof.
  intros t u H; induction H; intros rho depth; try solve [cbn [instantiate]; constructor; auto].
  - apply red_root; now apply instantiate_root_step.
  - cbn [instantiate].
    replace (S depth) with (1+depth) by lia; rewrite instantiate_lift by lia.
    apply red_eta.
Qed.
Theorem instantiation_reflects_normalization : forall t rho k,
  full_SN (instantiate rho k t) -> full_SN t.
Proof.
  intros t rho k H; eapply full_SN_map_reflection with (C:=instantiate rho k);
    [intros; now apply reduction_instantiate|exact H].
Qed.
Lemma reductions_instantiate : forall t u, rtc reduction t u -> forall rho k,
  rtc reduction (instantiate rho k t) (instantiate rho k u).
Proof.
  intros t u HR rho k; eapply (@rtc_map_rel term term reduction reduction (instantiate rho k));
    [intros; now apply reduction_instantiate|exact HR].
Qed.
Lemma conversion_instantiate : forall t u, conv t u -> forall rho k,
  conv (instantiate rho k t) (instantiate rho k u).
Proof.
  intros t u HC rho k; destruct (conversion_joinable _ _ HC) as [v [Ht Hu]].
  eapply cv_trans; [apply reductions_conversion; exact (reductions_instantiate _ _ Ht rho k)|].
  apply cv_sym, reductions_conversion; exact (reductions_instantiate _ _ Hu rho k).
Qed.
Lemma universe_le_instantiate : forall A B, universe_le A B -> forall rho k,
  universe_le (instantiate rho k A) (instantiate rho k B).
Proof. intros A B H; induction H; intros rho depth; cbn [instantiate]; constructor; auto. Qed.

Print Assumptions reduction_instantiate.
Print Assumptions instantiation_reflects_normalization.
Print Assumptions conversion_instantiate.

Lemma instantiate_variable : forall rho n, instantiate rho 0 (TVar n) = rho n.
Proof. intros; cbn [instantiate]; now rewrite Nat.sub_0_r, lift_zero_id. Qed.
Definition semantic_environment Gamma (rho : nat -> term) := forall n A,
  nth_error Gamma n = Some A -> semantic_value (rho n) (instantiate rho 0 (lift (S n) 0 A)).
Lemma semantic_environment_empty : forall rho, semantic_environment nil rho.
Proof. intros rho n A H; destruct n; discriminate. Qed.
Lemma semantic_environment_extend : forall Gamma rho A a,
  semantic_environment Gamma rho -> semantic_value a (instantiate rho 0 A) ->
  semantic_environment (A :: Gamma) (extend_substitution a rho).
Proof.
  intros Gamma rho A a HE Ha n B HB; destruct n.
  - cbn in HB; inversion HB; subst B.
    change (semantic_value a (instantiate (extend_substitution a rho) 0 (lift 1 0 A))).
    now rewrite instantiate_cons_lift.
  - change (semantic_value (rho n) (instantiate (extend_substitution a rho) 0 (lift (S (S n)) 0 B))).
    replace (lift (S (S n)) 0 B) with (lift 1 0 (lift (S n) 0 B)) by
      (apply lift_fuse_zero; lia).
    rewrite instantiate_cons_lift.
    now apply HE.
Qed.
Lemma semantic_environment_variable : forall Gamma rho n A,
  semantic_environment Gamma rho -> nth_error Gamma n = Some A ->
  semantic_value (instantiate rho 0 (TVar n)) (instantiate rho 0 (lift (S n) 0 A)).
Proof. intros; rewrite instantiate_variable; now apply H. Qed.

Print Assumptions semantic_environment_extend.
