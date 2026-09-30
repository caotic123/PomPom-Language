Require Import Progress.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.

(* Structural conversion, with the opaque [mu^S] application treated as an
   atomic conversion class.  The ordinary application constructor is retained
   as well: [me_muapp] is an additional, intentionally overlapping case. *)
Inductive mueq : term -> term -> Prop :=
| me_var : forall n, mueq (TVar n) (TVar n)
| me_sort : forall k, mueq (TSort k) (TSort k)
| me_pi : forall A A' B B', mueq A A' -> mueq B B' -> mueq (TPi A B) (TPi A' B')
| me_lam : forall b b', mueq b b' -> mueq (TLam b) (TLam b')
| me_app : forall f f' a a', mueq f f' -> mueq a a' -> mueq (TApp f a) (TApp f' a')
| me_muapp : forall S1 S2 i1 i2,
    conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
    mueq (TApp (TMuS S1) i1) (TApp (TMuS S2) i2)
| me_sigma : forall A A' B B', mueq A A' -> mueq B B' -> mueq (TSigma A B) (TSigma A' B')
| me_pair : forall a a' b b', mueq a a' -> mueq b b' -> mueq (TPair a b) (TPair a' b')
| me_fst : forall p p', mueq p p' -> mueq (TFst p) (TFst p')
| me_snd : forall p p', mueq p p' -> mueq (TSnd p) (TSnd p')
| me_unitt : mueq TUnitT TUnitT
| me_unit : mueq TUnit TUnit
| me_uid : mueq TUId TUId
| me_tag : forall s, mueq (TTag s) (TTag s)
| me_enumu : mueq TEnumU TEnumU
| me_nile : mueq TNilE TNilE
| me_conse : forall t t' E E', mueq t t' -> mueq E E' -> mueq (TConsE t E) (TConsE t' E')
| me_enumt : forall E E', mueq E E' -> mueq (TEnumT E) (TEnumT E')
| me_ezero : mueq TEZero TEZero
| me_esucc : forall n n', mueq n n' -> mueq (TESucc n) (TESucc n')
| me_epi : forall E E' P P', mueq E E' -> mueq P P' -> mueq (TEPi E P) (TEPi E' P')
| me_switch : forall E E' P P' p p' e e',
    mueq E E' -> mueq P P' -> mueq p p' -> mueq e e' ->
    mueq (TSwitch E P p e) (TSwitch E' P' p' e')
| me_idesc : forall I I', mueq I I' -> mueq (TIDesc I) (TIDesc I')
| me_ivar : forall i i', mueq i i' -> mueq (TIVar i) (TIVar i')
| me_i1 : mueq TI1 TI1
| me_iprod : forall A A' B B', mueq A A' -> mueq B B' -> mueq (TIProd A B) (TIProd A' B')
| me_ipi : forall S S' T T', mueq S S' -> mueq T T' -> mueq (TIPi S T) (TIPi S' T')
| me_isig : forall S S' T T', mueq S S' -> mueq T T' -> mueq (TISig S T) (TISig S' T')
| me_ichoice : forall E E' T T', mueq E E' -> mueq T T' -> mueq (TIChoice E T) (TIChoice E' T')
| me_interp : forall D D' X X', mueq D D' -> mueq X X' -> mueq (TInterp D X) (TInterp D' X')
| me_mui : forall R R', mueq R R' -> mueq (TMuI R) (TMuI R')
| me_mus : forall S S', mueq S S' -> mueq (TMuS S) (TMuS S')
| me_in : forall x x', mueq x x' -> mueq (TIn x) (TIn x')
| me_ind : forall R R' P P' s s' i i' x x',
    mueq R R' -> mueq P P' -> mueq s s' -> mueq i i' -> mueq x x' ->
    mueq (TInd R P s i x) (TInd R' P' s' i' x')
| me_iall : forall D D' X X' xs xs' P P',
    mueq D D' -> mueq X X' -> mueq xs xs' -> mueq P P' ->
    mueq (TIAll D X xs P) (TIAll D' X' xs' P')
| me_hyps : forall D D' X X' P P' h h' xs xs',
    mueq D D' -> mueq X X' -> mueq P P' -> mueq h h' -> mueq xs xs' ->
    mueq (THyps D X P h xs) (THyps D' X' P' h' xs')
| me_list : forall A A', mueq A A' -> mueq (TList A) (TList A')
| me_lnil : forall A A', mueq A A' -> mueq (TLNil A) (TLNil A')
| me_lcons : forall A A' a a' l l',
    mueq A A' -> mueq a a' -> mueq l l' ->
    mueq (TLCons A a l) (TLCons A' a' l')
| me_case : forall M M' Q Q' bs bs',
    mueq M M' -> mueq Q Q' -> mubeq bs bs' ->
    mueq (TCase M Q bs) (TCase M' Q' bs')
with mubeq : list (term * term) -> list (term * term) -> Prop :=
| mbe_nil : mubeq [] []
| mbe_cons : forall c c' b b' bs bs',
    mueq c c' -> mueq b b' -> mubeq bs bs' ->
    mubeq ((c,b)::bs) ((c',b')::bs').

Scheme mueq_ind' := Induction for mueq Sort Prop
with mubeq_ind' := Induction for mubeq Sort Prop.
Combined Scheme mueq_mubeq_ind from mueq_ind', mubeq_ind'.

Lemma mueq_refl_mut :
    (forall t, mueq t t) /\ (forall bs, mubeq bs bs).
Proof.
  assert (Hbranches : forall bs,
      (forall c b, In (c,b) bs -> mueq c c /\ mueq b b) -> mubeq bs bs).
  {
    intros bs. induction bs as [|[c b] bs IH]; intros H.
    - constructor.
    - constructor.
      + exact (proj1 (H c b (or_introl eq_refl))).
      + exact (proj2 (H c b (or_introl eq_refl))).
      + apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  assert (Hterm : forall t, mueq t t).
  {
    apply (tsize_strong_ind (fun t => mueq t t)).
    intros t IH. destruct t; cbn;
      try pose proof (tsize_pos t) as Ht;
      try pose proof (tsize_pos t1) as Ht1;
      try pose proof (tsize_pos t2) as Ht2;
      try pose proof (tsize_pos t3) as Ht3;
      try pose proof (tsize_pos t4) as Ht4;
      try pose proof (tsize_pos t5) as Ht5.
    all: try solve [constructor].
    all: try solve [constructor; repeat (apply IH; cbn; lia)].
    match goal with
    | |- mueq (TCase ?M ?Q ?bs) (TCase ?M ?Q ?bs) =>
        apply me_case;
          [apply IH; cbn; lia |
           apply IH; cbn; lia |
           apply Hbranches; intros c b Hin; split;
             [apply IH; eapply tsize_case_bs; exact Hin |
              apply IH; eapply tsize_case_bs_body; exact Hin]]
    end.
  }
  split; [exact Hterm |].
  intros bs. induction bs as [|[c b] bs IH].
    + constructor.
    + constructor; [apply Hterm | apply Hterm | exact IH].
Qed.

Lemma mueq_refl : forall t, mueq t t.
Proof. exact (proj1 mueq_refl_mut). Qed.

Lemma mubeq_refl : forall bs, mubeq bs bs.
Proof. exact (proj2 mueq_refl_mut). Qed.

Ltac mconv_congr :=
  eauto 12 using cv_refl, cv_pi, cv_lam, cv_app, cv_sigma, cv_pair,
    cv_fst, cv_snd, cv_conse, cv_enumt, cv_esucc, cv_epi, cv_switch,
    cv_idesc, cv_ivar, cv_iprod, cv_ipi, cv_isig, cv_ichoice,
    cv_interp, cv_mui, cv_mus, cv_in, cv_ind, cv_iall, cv_hyps,
    cv_list, cv_lnil, cv_lcons.

Lemma mueq_conv_mut :
    (forall t u, mueq t u -> conv t u) /\
    (forall bs bs', mubeq bs bs' -> forall pre M Q,
      conv (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply mueq_mubeq_ind; intros;
    try solve [mconv_congr];
    try solve [exact H].
  - eapply cv_trans.
    + eapply cv_case; eauto.
    + specialize (H1 [] M' Q'). cbn in H1. exact H1.
  - change (conv
      (TCase M Q (pre ++ (c,b) :: bs))
      (TCase M Q (pre ++ (c',b') :: bs'))).
    eapply cv_trans.
    + apply cv_case_br; eauto.
    + specialize (H1 (pre ++ [(c',b')]) M Q).
      repeat rewrite <- app_assoc in H1. cbn in H1. exact H1.
Qed.

Lemma mueq_conv : forall t u, mueq t u -> conv t u.
Proof. intros t u H. exact (proj1 mueq_conv_mut t u H). Qed.

Lemma mubeq_case_conv : forall bs bs', mubeq bs bs' -> forall pre M Q,
    conv (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs')).
Proof. intros bs bs' H. exact (proj2 mueq_conv_mut bs bs' H). Qed.
