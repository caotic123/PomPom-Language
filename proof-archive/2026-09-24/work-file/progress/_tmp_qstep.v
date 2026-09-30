Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Inductive qstep : term -> term -> Prop :=
| qs_var : forall n, qstep (TVar n) (TVar n)
| qs_sort : forall k, qstep (TSort k) (TSort k)
| qs_pi : forall A A' B B', qstep A A' -> qstep B B' ->
    qstep (TPi A B) (TPi A' B')
| qs_lam : forall b b', qstep b b' -> qstep (TLam b) (TLam b')
| qs_app : forall f f' a a', qstep f f' -> qstep a a' ->
    qstep (TApp f a) (TApp f' a')
| qs_sigma : forall A A' B B', qstep A A' -> qstep B B' ->
    qstep (TSigma A B) (TSigma A' B')
| qs_pair : forall a a' b b', qstep a a' -> qstep b b' ->
    qstep (TPair a b) (TPair a' b')
| qs_fst : forall p p', qstep p p' -> qstep (TFst p) (TFst p')
| qs_snd : forall p p', qstep p p' -> qstep (TSnd p) (TSnd p')
| qs_unitt : qstep TUnitT TUnitT
| qs_unit : qstep TUnit TUnit
| qs_uid : qstep TUId TUId
| qs_tag : forall s, qstep (TTag s) (TTag s)
| qs_enumu : qstep TEnumU TEnumU
| qs_nile : qstep TNilE TNilE
| qs_conse : forall t t' E E', qstep t t' -> qstep E E' ->
    qstep (TConsE t E) (TConsE t' E')
| qs_enumt : forall E E', qstep E E' -> qstep (TEnumT E) (TEnumT E')
| qs_ezero : qstep TEZero TEZero
| qs_esucc : forall n n', qstep n n' -> qstep (TESucc n) (TESucc n')
| qs_epi : forall E E' P P', qstep E E' -> qstep P P' ->
    qstep (TEPi E P) (TEPi E' P')
| qs_switch : forall E E' P P' p p' e e',
    qstep E E' -> qstep P P' -> qstep p p' -> qstep e e' ->
    qstep (TSwitch E P p e) (TSwitch E' P' p' e')
| qs_idesc : forall I I', qstep I I' -> qstep (TIDesc I) (TIDesc I')
| qs_ivar : forall i i', qstep i i' -> qstep (TIVar i) (TIVar i')
| qs_i1 : qstep TI1 TI1
| qs_iprod : forall A A' B B', qstep A A' -> qstep B B' ->
    qstep (TIProd A B) (TIProd A' B')
| qs_ipi : forall S S' T T', qstep S S' -> qstep T T' ->
    qstep (TIPi S T) (TIPi S' T')
| qs_isig : forall S S' T T', qstep S S' -> qstep T T' ->
    qstep (TISig S T) (TISig S' T')
| qs_ichoice : forall E E' T T', qstep E E' -> qstep T T' ->
    qstep (TIChoice E T) (TIChoice E' T')
| qs_interp : forall D D' X X', qstep D D' -> qstep X X' ->
    qstep (TInterp D X) (TInterp D' X')
| qs_mui : forall R R', qstep R R' -> qstep (TMuI R) (TMuI R')
| qs_mus : forall S S', qstep S S' -> qstep (TMuS S) (TMuS S')
| qs_in : forall x x', qstep x x' -> qstep (TIn x) (TIn x')
| qs_ind : forall R R' P P' s s' i i' x x',
    qstep R R' -> qstep P P' -> qstep s s' -> qstep i i' -> qstep x x' ->
    qstep (TInd R P s i x) (TInd R' P' s' i' x')
| qs_iall : forall D D' X X' xs xs' P P',
    qstep D D' -> qstep X X' -> qstep xs xs' -> qstep P P' ->
    qstep (TIAll D X xs P) (TIAll D' X' xs' P')
| qs_hyps : forall D D' X X' P P' h h' xs xs',
    qstep D D' -> qstep X X' -> qstep P P' -> qstep h h' -> qstep xs xs' ->
    qstep (THyps D X P h xs) (THyps D' X' P' h' xs')
| qs_list : forall A A', qstep A A' -> qstep (TList A) (TList A')
| qs_lnil : forall A A', qstep A A' -> qstep (TLNil A) (TLNil A')
| qs_lcons : forall A A' a a' l l',
    qstep A A' -> qstep a a' -> qstep l l' ->
    qstep (TLCons A a l) (TLCons A' a' l')
| qs_case : forall M M' Q Q' bs bs',
    qstep M M' -> qstep Q Q' -> qbranches bs bs' ->
    qstep (TCase M Q bs) (TCase M' Q' bs')

(* root contractions, with every metavariable developed in parallel *)
| qs_beta : forall b b' a a', qstep b b' -> qstep a a' ->
    qstep (TApp (TLam b) a) (subst a' 0 b')
| qs_fst_pair : forall a a' b b', qstep a a' -> qstep b b' ->
    qstep (TFst (TPair a b)) a'
| qs_snd_pair : forall a a' b b', qstep a a' -> qstep b b' ->
    qstep (TSnd (TPair a b)) b'
| qs_epi_nil : forall P P', qstep P P' -> qstep (TEPi TNilE P) TUnitT
| qs_epi_cons : forall tg tg' E E' P P',
    qstep tg tg' -> qstep E E' -> qstep P P' ->
    qstep (TEPi (TConsE tg E) P)
      (TSigma (TApp P' TEZero)
        (lift 1 0 (TEPi E' (TLam (TApp (lift 1 0 P') (TESucc (TVar 0)))))))
| qs_switch_zero : forall tg tg' E E' P P' p0 p0' ps ps',
    qstep tg tg' -> qstep E E' -> qstep P P' ->
    qstep p0 p0' -> qstep ps ps' ->
    qstep (TSwitch (TConsE tg E) P (TPair p0 ps) TEZero) p0'
| qs_switch_succ : forall tg tg' E E' P P' p0 p0' ps ps' n n',
    qstep tg tg' -> qstep E E' -> qstep P P' ->
    qstep p0 p0' -> qstep ps ps' -> qstep n n' ->
    qstep (TSwitch (TConsE tg E) P (TPair p0 ps) (TESucc n))
      (TSwitch E' (TLam (TApp (lift 1 0 P') (TESucc (TVar 0)))) ps' n')
| qs_interp_var : forall i i' X X', qstep i i' -> qstep X X' ->
    qstep (TInterp (TIVar i) X) (TApp X' i')
| qs_interp_one : forall X X', qstep X X' ->
    qstep (TInterp TI1 X) TUnitT
| qs_interp_prod : forall A A' B B' X X',
    qstep A A' -> qstep B B' -> qstep X X' ->
    qstep (TInterp (TIProd A B) X)
      (TSigma (TInterp A' X') (lift 1 0 (TInterp B' X')))
| qs_interp_pi : forall S S' T T' X X',
    qstep S S' -> qstep T T' -> qstep X X' ->
    qstep (TInterp (TIPi S T) X)
      (TPi S' (TInterp (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')))
| qs_interp_sig : forall S S' T T' X X',
    qstep S S' -> qstep T T' -> qstep X X' ->
    qstep (TInterp (TISig S T) X)
      (TSigma S' (TInterp (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')))
| qs_interp_choice : forall E E' T T' X X',
    qstep E E' -> qstep T T' -> qstep X X' ->
    qstep (TInterp (TIChoice E T) X)
      (TSigma (TEnumT E')
        (TInterp (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')))
| qs_iall_var : forall j j' X X' x x' P P',
    qstep j j' -> qstep X X' -> qstep x x' -> qstep P P' ->
    qstep (TIAll (TIVar j) X x P) (TApp P' (TPair j' x'))
| qs_iall_one : forall X X' P P', qstep X X' -> qstep P P' ->
    qstep (TIAll TI1 X TUnit P) TUnitT
| qs_iall_prod : forall A A' B B' X X' a a' b b' P P',
    qstep A A' -> qstep B B' -> qstep X X' ->
    qstep a a' -> qstep b b' -> qstep P P' ->
    qstep (TIAll (TIProd A B) X (TPair a b) P)
      (TSigma (TIAll A' X' a' P') (lift 1 0 (TIAll B' X' b' P')))
| qs_iall_pi : forall S S' T T' X X' f f' P P',
    qstep S S' -> qstep T T' -> qstep X X' -> qstep f f' -> qstep P P' ->
    qstep (TIAll (TIPi S T) X f P)
      (TPi S' (TIAll (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')
                    (TApp (lift 1 0 f') (TVar 0)) (lift 1 0 P')))
| qs_iall_sig : forall S S' T T' X X' s s' x x' P P',
    qstep S S' -> qstep T T' -> qstep X X' ->
    qstep s s' -> qstep x x' -> qstep P P' ->
    qstep (TIAll (TISig S T) X (TPair s x) P)
      (TIAll (TApp T' s') X' x' P')
| qs_iall_choice : forall E E' T T' X X' e e' x x' P P',
    qstep E E' -> qstep T T' -> qstep X X' ->
    qstep e e' -> qstep x x' -> qstep P P' ->
    qstep (TIAll (TIChoice E T) X (TPair e x) P)
      (TIAll (TApp T' e') X' x' P')
| qs_hyqs_var : forall j j' X X' P P' h h' x x',
    qstep j j' -> qstep X X' -> qstep P P' -> qstep h h' -> qstep x x' ->
    qstep (THyps (TIVar j) X P h x) (TApp (TApp h' j') x')
| qs_hyqs_one : forall X X' P P' h h',
    qstep X X' -> qstep P P' -> qstep h h' ->
    qstep (THyps TI1 X P h TUnit) TUnit
| qs_hyqs_prod : forall A A' B B' X X' P P' h h' a a' b b',
    qstep A A' -> qstep B B' -> qstep X X' -> qstep P P' ->
    qstep h h' -> qstep a a' -> qstep b b' ->
    qstep (THyps (TIProd A B) X P h (TPair a b))
      (TPair (THyps A' X' P' h' a') (THyps B' X' P' h' b'))
| qs_hyqs_pi : forall S S' T T' X X' P P' h h' f f',
    qstep S S' -> qstep T T' -> qstep X X' -> qstep P P' ->
    qstep h h' -> qstep f f' ->
    qstep (THyps (TIPi S T) X P h f)
      (TLam (THyps (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')
                    (lift 1 0 P') (lift 1 0 h')
                    (TApp (lift 1 0 f') (TVar 0))))
| qs_hyqs_sig : forall S S' T T' X X' P P' h h' s s' x x',
    qstep S S' -> qstep T T' -> qstep X X' -> qstep P P' ->
    qstep h h' -> qstep s s' -> qstep x x' ->
    qstep (THyps (TISig S T) X P h (TPair s x))
      (THyps (TApp T' s') X' P' h' x')
| qs_hyqs_choice : forall E E' T T' X X' P P' h h' e e' x x',
    qstep E E' -> qstep T T' -> qstep X X' -> qstep P P' ->
    qstep h h' -> qstep e e' -> qstep x x' ->
    qstep (THyps (TIChoice E T) X P h (TPair e x))
      (THyps (TApp T' e') X' P' h' x')
| qs_ind_red : forall R R' P P' s s' i i' xs xs',
    qstep R R' -> qstep P P' -> qstep s s' -> qstep i i' -> qstep xs xs' ->
    qstep (TInd R P s i (TIn xs))
      (TApp (TApp (TApp s' i') xs')
        (THyps (TApp R' i') (TMuI R') P'
          (TLam (TLam (TInd (lift 2 0 R') (lift 2 0 P') (lift 2 0 s')
                            (TVar 1) (TVar 0)))) xs'))
| qs_case_red : forall a xs xs' Q bs k c b b' n,
    nth_error bs k = Some (c,b) -> enum_pos c n -> enum_pos a n ->
    (forall j cj bj, j < k -> nth_error bs j = Some (cj,bj) ->
       exists nj, enum_pos cj nj /\ nj <> n) ->
    qstep xs xs' -> qstep b b' ->
    qstep (TCase (TIn (TPair a xs)) Q bs) (subst xs' 0 b')

| qs_eta : forall f f', qstep f f' ->
    qstep (TLam (TApp (lift 1 0 f) (TVar 0))) f'

with qbranches : list (term * term) -> list (term * term) -> Prop :=
| qbs_nil : qbranches [] []
| qbs_cons : forall c c' b b' bs bs',
    qstep c c' -> qstep b b' -> qbranches bs bs' ->
    qbranches ((c,b)::bs) ((c',b')::bs').

Scheme qstep_ind' := Induction for qstep Sort Prop
with qbranches_ind' := Induction for qbranches Sort Prop.
Combined Scheme qstep_qbranches_ind from qstep_ind', qbranches_ind'.

Lemma qstep_refl : forall t, qstep t t.
Proof.
  apply (tsize_strong_ind (fun t => qstep t t)).
  intros t IH. destruct t;
    try pose proof (tsize_pos t) as Ht;
    try pose proof (tsize_pos t1) as Ht1;
    try pose proof (tsize_pos t2) as Ht2;
    try pose proof (tsize_pos t3) as Ht3;
    try pose proof (tsize_pos t4) as Ht4;
    try pose proof (tsize_pos t5) as Ht5;
    try solve [constructor];
    try (constructor;
      repeat (apply IH; cbn; lia)).
  match goal with
  | IH : forall u, tsize u < tsize (TCase ?M ?Q ?bs) -> qstep u u
      |- qbranches ?bs ?bs =>
      assert (HB : forall c b, In (c,b) bs -> qstep c c /\ qstep b b)
        by (intros c b Hin; split; apply IH;
            [eapply tsize_case_bs | eapply tsize_case_bs_body]; exact Hin);
      clear IH;
      induction bs as [|[c b] bs IHbs]; [constructor |];
      constructor;
      [ exact (proj1 (HB c b (or_introl eq_refl)))
      | exact (proj2 (HB c b (or_introl eq_refl)))
      | apply IHbs; intros; apply HB; right; assumption ]
  end.
Qed.

Lemma qstep_lift_mut :
  (forall t u (H : qstep t u), forall d k,
      qstep (lift d k t) (lift d k u)) /\
  (forall bs bs' (H : qbranches bs bs'), forall d k,
      qbranches
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs')).
Proof.
  apply qstep_qbranches_ind; cbn; intros;
    try solve [constructor; eauto using qstep_refl].
  - apply qstep_refl.
  - rewrite lift_subst_zero_comm. eapply qs_beta; eauto.
  - eapply qs_fst_pair; eauto.
  - eapply qs_snd_pair; eauto.
  - eapply qs_epi_nil; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    repeat rewrite (lift_lift_one_one _ d k).
    repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_epi_cons; eauto.
  - eapply qs_switch_zero; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_switch_succ; eauto.
  - eapply qs_interp_one; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_interp_prod; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_interp_pi; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_interp_sig; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_interp_choice; eauto.
  - eapply qs_iall_var; eauto.
  - eapply qs_iall_one; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_iall_prod; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_iall_pi; eauto.
  - eapply qs_iall_sig; eauto.
  - eapply qs_iall_choice; eauto.
  - eapply qs_hyqs_var; eauto.
  - eapply qs_hyqs_one; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_hyqs_pi; eauto.
  - eapply qs_hyqs_sig; eauto.
  - eapply qs_hyqs_choice; eauto.
  - repeat rewrite (lift_lift_two_zero _ d k).
    eapply qs_ind_red; eauto.
  - rewrite lift_subst_zero_comm.
    eapply qs_case_red with
      (k:=k) (c:=lift d k0 c) (b:=lift d (S k0) b) (n:=n).
    + eapply nth_error_lift_branches. exact e.
    + rewrite (enum_pos_lift_id c n e0 d k0). exact e0.
    + rewrite (enum_pos_lift_id a n e1 d k0). exact e1.
    + intros j cj bj Hj Hnth.
      rewrite nth_error_map in Hnth.
      destruct (nth_error bs j) as [[cj0 bj0]|] eqn:Horig;
        cbn in Hnth; [|discriminate].
      inversion Hnth; subst cj bj.
      destruct (e2 j cj0 bj0 Hj Horig) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite (enum_pos_lift_id cj0 nj Hpos d k0). exact Hpos.
      * exact Hneq.
    + apply H.
    + apply H0.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply qs_eta; eauto.
Qed.

Corollary qstep_lift : forall t u, qstep t u -> forall d k,
    qstep (lift d k t) (lift d k u).
Proof. intros t u H. exact (proj1 qstep_lift_mut t u H). Qed.

Corollary qbranches_lift : forall bs bs', qbranches bs bs' -> forall d k,
    qbranches
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs').
Proof. intros bs bs' H. exact (proj2 qstep_lift_mut bs bs' H). Qed.
Lemma qstep_subst_mut :
  (forall t t' (H : qstep t t'), forall u u' k,
      qstep u u' -> qstep (subst u k t) (subst u' k t')) /\
  (forall bs bs' (H : qbranches bs bs'), forall u u' k,
      qstep u u' ->
      qbranches
        (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
        (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) bs')).
Proof.
  apply qstep_qbranches_ind; cbn; intros;
    try solve [constructor; eauto using qstep_refl, qstep_lift].
  - change (qstep (subst u k (TVar n)) (subst u' k (TVar n))).
    destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
    + assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
      cbn [subst]. rewrite Hlt. apply qstep_refl.
    + subst n.
      assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
      cbn [subst]. rewrite Hlt, Heq. eapply qstep_lift. exact H.
    + assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
      cbn [subst]. rewrite Hlt, Heq. apply qstep_refl.
  - rewrite subst_subst_zero_comm. eapply qs_beta; eauto.
  - eapply qs_fst_pair; eauto.
  - eapply qs_snd_pair; eauto.
  - eapply qs_epi_nil; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    repeat rewrite (subst_lift_one_one _ u' k).
    repeat rewrite (subst_lift_one_zero _ u' k).
    eapply qs_epi_cons; eauto.
  - eapply qs_switch_zero; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply qs_switch_succ; eauto.
  - eapply qs_interp_one; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply qs_interp_prod; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply qs_interp_pi; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply qs_interp_sig; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply qs_interp_choice; eauto.
  - eapply qs_iall_var; eauto.
  - eapply qs_iall_one; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply qs_iall_prod; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply qs_iall_pi; eauto.
  - eapply qs_iall_sig; eauto.
  - eapply qs_iall_choice; eauto.
  - eapply qs_hyqs_var; eauto.
  - eapply qs_hyqs_one; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply qs_hyqs_pi; eauto.
  - eapply qs_hyqs_sig; eauto.
  - eapply qs_hyqs_choice; eauto.
  - repeat rewrite (subst_lift_two_zero _ u' k).
    eapply qs_ind_red; eauto.
  - rewrite subst_subst_zero_comm.
    eapply qs_case_red with
      (k:=k) (c:=subst u k0 c) (b:=subst u (S k0) b) (n:=n).
    + eapply nth_error_subst_branches. exact e.
    + rewrite (enum_pos_subst_id c n e0 u k0). exact e0.
    + rewrite (enum_pos_subst_id a n e1 u k0). exact e1.
    + intros j cj bj Hj Hnth.
      rewrite nth_error_map in Hnth.
      destruct (nth_error bs j) as [[cj0 bj0]|] eqn:Horig;
        cbn in Hnth; [|discriminate].
      inversion Hnth; subst cj bj.
      destruct (e2 j cj0 bj0 Hj Horig) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite (enum_pos_subst_id cj0 nj Hpos u k0). exact Hpos.
      * exact Hneq.
    + eauto.
    + eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    repeat rewrite (subst_lift_one_zero _ u k).
    eapply qs_eta; eauto.
Qed.

Corollary qstep_subst : forall t t', qstep t t' -> forall u u' k,
    qstep u u' -> qstep (subst u k t) (subst u' k t').
Proof. intros t t' H. exact (proj1 qstep_subst_mut t t' H). Qed.

Corollary qbranches_subst : forall bs bs', qbranches bs bs' ->
    forall u u' k, qstep u u' ->
    qbranches
      (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
      (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) bs').
Proof. intros bs bs' H. exact (proj2 qstep_subst_mut bs bs' H). Qed.


