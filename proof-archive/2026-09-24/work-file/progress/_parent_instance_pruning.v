(* Directed pruning of explicit signature instances. *)
Require Import Progress SignatureConversion SignatureInstances ErasureCounterexample.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules Progress._tmp_epstep
 Progress._tmp_epstep_subst Progress._tmp_commute
 Progress._work_mixed_closure Progress._work_cjoin
 Progress._work_cstep_invariants Progress._work_conv_whd_pos
 Progress._luna_phi_erase_shapes Progress.MuApplicationSort.

Theorem pruning_step_subst : forall t v, step t v -> forall u k,
    step (subst u k t) (subst u k v).
Proof.
  intros t v H.
  induction H; intros u kk;
    try solve [cbn; constructor; eauto];
    try solve [cbn;
               repeat rewrite subst_lift_one_zero;
               repeat rewrite subst_lift_one_one;
               repeat rewrite subst_lift_one_zero;
               repeat rewrite subst_lift_two_zero;
               constructor];
    try solve [cbn; rewrite subst_subst_zero_comm; constructor].
  - (* st_case: raw case reduction — the side conditions transport through
       nth_error_subst_branches and enum_pos_subst_id; case bodies keep
       cutoff S k. *)
    cbn. rewrite subst_subst_zero_comm.
    eapply st_case with (k := k) (c := subst u kk c) (b := subst u (S kk) b)
                         (n := n).
    + eapply nth_error_subst_branches; exact H.
    + rewrite (enum_pos_subst_id c n H0 u kk). exact H0.
    + rewrite (enum_pos_subst_id a n H1 u kk). exact H1.
    + intros j cj bj Hj Hnthj.
      rewrite nth_error_map in Hnthj.
      destruct (nth_error bs j) as [[cj0 bj0]|] eqn:Horig;
        cbn in Hnthj; [|discriminate].
      inversion Hnthj; subst.
      destruct (H2 j cj0 bj0 Hj Horig) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite (enum_pos_subst_id cj0 nj Hpos u kk). exact Hpos.
      * exact Hneq.
  - (* st_case_lbl: clause labels evaluate in place — congruence under map. *)
    cbn. rewrite !map_app. cbn [map].
    constructor; eauto.
Qed.
Theorem pruning_eval_subst : forall t v, eval t v -> forall u k,
    eval (subst u k t) (subst u k v).
Proof.
  intros t v H.
  induction H as [t | t w v Hst Heval IH]; intros u k.
  - (* ev_refl *)
    apply ev_refl.
  - (* ev_step *)
    eapply ev_step.
    + exact (pruning_step_subst _ _ Hst u k).
    + exact (IH u k).
Qed.

Theorem pruning_against_subst : forall D, desc_against D -> forall u k,
    desc_against (subst u k D).
Proof.
  intros D H.
  induction H as
    [ D0 E T Hnil Hecons
    | D0 A B HprodL HdescL IHprodL
    | D0 A B HprodR HdescR IHprodR
    | D0 E T tg E' Hch Hecons Hzero IHzero Hcons IHcons ]; intros u k; cbn.
  - (* ag_choice_nil *)
    apply (@ag_choice_nil (subst u k D0) (subst u k E) (subst u k T)).
    + exact (pruning_eval_subst _ _ Hnil u k).
    + exact (pruning_eval_subst _ _ Hecons u k).
  - (* ag_prod_left *)
    apply (@ag_prod_left (subst u k D0) (subst u k A) (subst u k B)).
    + exact (pruning_eval_subst _ _ HprodL u k).
    + exact (IHprodL u k).
  - (* ag_prod_right *)
    apply (@ag_prod_right (subst u k D0) (subst u k A) (subst u k B)).
    + exact (pruning_eval_subst _ _ HprodR u k).
    + exact (IHprodR u k).
  - (* ag_choice_cons *)
    apply (@ag_choice_cons (subst u k D0) (subst u k E) (subst u k T)
                            (subst u k tg) (subst u k E')).
    + exact (pruning_eval_subst _ _ Hch u k).
    + exact (pruning_eval_subst _ _ Hecons u k).
    + exact (IHzero u k).
    + rewrite <- (subst_lift_one_zero T u k). exact (IHcons u k).
Qed.

Definition instance_dead (D : term) : Prop :=
  exists D0, desc_against D0 /\ cjoin (phi_erase D) (phi_erase D0).

Lemma instance_dead_join : forall D D',
  cjoin (phi_erase D) (phi_erase D') -> instance_dead D -> instance_dead D'.
Proof.
  intros D D' H [D0 [HD0 Hj]]. exists D0. split; [exact HD0|].
  eapply cjoin_trans; [apply cjoin_sym; exact H|exact Hj].
Qed.

Lemma instance_dead_subst : forall D u k,
  instance_dead D -> instance_dead (subst u k D).
Proof.
  intros D u k [D0 [HD0 [w [H1 H2]]]].
  exists (subst u k D0). split; [apply pruning_against_subst; exact HD0|].
  rewrite !phi_erase_subst.
  exists (subst (phi_erase u) k w). split;
    apply rtc_cstep_subst_luna; assumption.
Qed.

Lemma instance_dead_progress : forall N D xs T X,
  bounded_progress_parent N -> tsize xs <= N -> check [] xs T ->
  cjoin (phi_erase T) (phi_erase (TInterp D X)) ->
  instance_dead D -> exists xs', step xs xs'.
Proof.
  intros N D xs T X HP Hsz HC HT [D0 [HD0 Hjoin]].
  eapply (desc_against_erased_step_parent N HP D0 HD0 xs T X Hsz HC).
  eapply cjoin_trans; [exact HT|].
  cbn. apply cjoin_interp_parent; [exact Hjoin|apply cjoin_refl].
Qed.

Inductive prune_term : term -> term -> Prop :=
| pt_var : forall n, prune_term (TVar n) (TVar n)
| pt_sort : forall k, prune_term (TSort k) (TSort k)
| pt_pi : forall A A' B B', prune_term A A' -> prune_term B B' -> prune_term (TPi A B) (TPi A' B')
| pt_lam : forall b b', prune_term b b' -> prune_term (TLam b) (TLam b')
| pt_app : forall f f' a a', prune_term f f' -> prune_term a a' -> prune_term (TApp f a) (TApp f' a')
| pt_sigma : forall A A' B B', prune_term A A' -> prune_term B B' -> prune_term (TSigma A B) (TSigma A' B')
| pt_pair : forall a a' b b', prune_term a a' -> prune_term b b' -> prune_term (TPair a b) (TPair a' b')
| pt_fst : forall p p', prune_term p p' -> prune_term (TFst p) (TFst p')
| pt_snd : forall p p', prune_term p p' -> prune_term (TSnd p) (TSnd p')
| pt_unitt : prune_term TUnitT TUnitT
| pt_unit : prune_term TUnit TUnit
| pt_uid : prune_term TUId TUId
| pt_tag : forall s, prune_term (TTag s) (TTag s)
| pt_enumu : prune_term TEnumU TEnumU
| pt_nile : prune_term TNilE TNilE
| pt_conse : forall t t' E E', prune_term t t' -> prune_term E E' -> prune_term (TConsE t E) (TConsE t' E')
| pt_enumt : forall E E', prune_term E E' -> prune_term (TEnumT E) (TEnumT E')
| pt_ezero : prune_term TEZero TEZero
| pt_esucc : forall n n', prune_term n n' -> prune_term (TESucc n) (TESucc n')
| pt_epi : forall E E' P P', prune_term E E' -> prune_term P P' -> prune_term (TEPi E P) (TEPi E' P')
| pt_switch : forall E E' P P' p p' e e',
    prune_term E E' -> prune_term P P' -> prune_term p p' -> prune_term e e' ->
    prune_term (TSwitch E P p e) (TSwitch E' P' p' e')
| pt_idesc : forall I I', prune_term I I' -> prune_term (TIDesc I) (TIDesc I')
| pt_ivar : forall i i', prune_term i i' -> prune_term (TIVar i) (TIVar i')
| pt_i1 : prune_term TI1 TI1
| pt_iprod : forall A A' B B', prune_term A A' -> prune_term B B' -> prune_term (TIProd A B) (TIProd A' B')
| pt_ipi : forall S S' T T', prune_term S S' -> prune_term T T' -> prune_term (TIPi S T) (TIPi S' T')
| pt_isig : forall S S' T T', prune_term S S' -> prune_term T T' -> prune_term (TISig S T) (TISig S' T')
| pt_ichoice : forall E E' T T', prune_term E E' -> prune_term T T' -> prune_term (TIChoice E T) (TIChoice E' T')
| pt_interp : forall D D' X X', prune_term D D' -> prune_term X X' -> prune_term (TInterp D X) (TInterp D' X')
| pt_mui : forall R R', prune_term R R' -> prune_term (TMuI R) (TMuI R')
| pt_mus : forall S S', prune_term S S' -> prune_term (TMuS S) (TMuS S')
| pt_instance : forall B B' L L', prune_term B B' -> prune_labels B L L' ->
    prune_term (TMuS (TPair B L)) (TMuS (TPair B' L'))
| pt_in : forall x x', prune_term x x' -> prune_term (TIn x) (TIn x')
| pt_ind : forall R R' P P' s s' i i' x x',
    prune_term R R' -> prune_term P P' -> prune_term s s' -> prune_term i i' -> prune_term x x' ->
    prune_term (TInd R P s i x) (TInd R' P' s' i' x')
| pt_iall : forall D D' X X' xs xs' P P',
    prune_term D D' -> prune_term X X' -> prune_term xs xs' -> prune_term P P' ->
    prune_term (TIAll D X xs P) (TIAll D' X' xs' P')
| pt_hyps : forall D D' X X' P P' h h' xs xs',
    prune_term D D' -> prune_term X X' -> prune_term P P' -> prune_term h h' -> prune_term xs xs' ->
    prune_term (THyps D X P h xs) (THyps D' X' P' h' xs')
| pt_list : forall A A', prune_term A A' -> prune_term (TList A) (TList A')
| pt_lnil : forall A A', prune_term A A' -> prune_term (TLNil A) (TLNil A')
| pt_lcons : forall A A' a a' l l',
    prune_term A A' -> prune_term a a' -> prune_term l l' ->
    prune_term (TLCons A a l) (TLCons A' a' l')
| pt_case : forall M M' Q Q' bs bs',
    prune_term M M' -> prune_term Q Q' -> prune_branches bs bs' ->
    prune_term (TCase M Q bs) (TCase M' Q' bs')
with prune_branches : list (term * term) -> list (term * term) -> Prop :=
| pb_nil : prune_branches [] []
| pb_cons : forall c c' b b' bs bs',
    prune_term c c' -> prune_term b b' -> prune_branches bs bs' ->
    prune_branches ((c,b)::bs) ((c',b')::bs')
with prune_labels : term -> term -> term -> Prop :=
| pl_stop : forall B L L', prune_term L L' -> prune_labels B L L'
| pl_keep : forall B A A' c c' L L',
    prune_term A A' -> prune_term c c' -> prune_labels B L L' ->
    prune_labels B (TLCons A c L) (TLCons A' c' L')
| pl_drop : forall B A c L L',
    instance_dead (TApp B c) -> prune_labels B L L' ->
    prune_labels B (TLCons A c L) L'.

Scheme prune_ind' := Induction for prune_term Sort Prop
with prune_branches_ind' := Induction for prune_branches Sort Prop
with prune_labels_ind' := Induction for prune_labels Sort Prop.
Combined Scheme prune_mut_ind from prune_ind', prune_branches_ind', prune_labels_ind'.
Lemma prune_term_refl_mut :
    (forall t, prune_term t t) /\ (forall bs, prune_branches bs bs).
Proof.
  assert (Hbranches : forall bs,
      (forall c b, In (c,b) bs -> prune_term c c /\ prune_term b b) -> prune_branches bs bs).
  {
    intros bs. induction bs as [|[c b] bs IH]; intros H.
    - constructor.
    - constructor.
      + exact (proj1 (H c b (or_introl eq_refl))).
      + exact (proj2 (H c b (or_introl eq_refl))).
      + apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  assert (Hterm : forall t, prune_term t t).
  {
    apply (tsize_strong_ind (fun t => prune_term t t)).
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
    | |- prune_term (TCase ?M ?Q ?bs) (TCase ?M ?Q ?bs) =>
        apply pt_case;
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

Lemma prune_term_refl : forall t, prune_term t t.
Proof. exact (proj1 prune_term_refl_mut). Qed.

Lemma prune_branches_refl : forall bs, prune_branches bs bs.
Proof. exact (proj2 prune_term_refl_mut). Qed.


Lemma prune_erase_mut :
  (forall t u, prune_term t u -> phi_erase t = phi_erase u) /\
  (forall bs cs, prune_branches bs cs ->
    map (fun '(c,b) => (phi_erase c, phi_erase b)) bs =
    map (fun '(c,b) => (phi_erase c, phi_erase b)) cs) /\
  (forall B L L', prune_labels B L L' -> True).
Proof.
  apply prune_mut_ind; cbn; intros; try reflexivity; try congruence; exact I.
Qed.
Lemma prune_erase : forall t u, prune_term t u -> phi_erase t = phi_erase u.
Proof. exact (proj1 prune_erase_mut). Qed.

Lemma prune_labels_rebase : forall B L L', prune_labels B L L' ->
  forall C, cjoin (phi_erase B) (phi_erase C) -> prune_labels C L L'.
Proof.
  intros B L L' H. induction H; intros C HBC.
  - apply pl_stop; assumption.
  - apply pl_keep; auto.
  - apply pl_drop; [|auto].
    eapply instance_dead_join; [|exact H].
    cbn. apply cjoin_app_parent; [exact HBC|apply cjoin_refl].
Qed.

Lemma prune_size_mut :
  (forall t u, prune_term t u -> tsize u <= tsize t) /\
  (forall bs cs, prune_branches bs cs -> bsize cs <= bsize bs) /\
  (forall B L L', prune_labels B L L' -> tsize L' <= tsize L).
Proof. apply prune_mut_ind; cbn; intros; lia. Qed.

Lemma prune_term_size : forall t u, prune_term t u -> tsize u <= tsize t.
Proof. exact (proj1 prune_size_mut). Qed.

Lemma prune_mus_pair_inv : forall B L u,
  prune_term (TMuS (TPair B L)) u ->
  exists B' L', u = TMuS (TPair B' L') /\
    prune_term B B' /\ prune_labels B L L'.
Proof.
  intros B L u H. inversion H; subst.
  - match goal with HP : prune_term (TPair _ _) _ |- _ => inversion HP; subst end.
    eexists; eexists. split; [reflexivity|]. split; [eassumption|].
    apply pl_stop; assumption.
  - eexists; eexists. repeat split; eassumption || reflexivity.
Qed.

Print Assumptions instance_dead_progress.
Print Assumptions prune_erase.
Print Assumptions prune_term_size.

Lemma pruning_eval_lift : forall d k t u,
  eval t u -> eval (lift d k t) (lift d k u).
Proof.
  intros d k t u H. induction H; eauto using eval, step_lift_glm.
Qed.
Lemma pruning_against_lift :
  forall D, desc_against D -> forall d k, desc_against (lift d k D).
Proof.
  intros D H.
  induction H as
    [ D0 E T Hnil Hecons
    | D0 A B HprodL HdescL IHprodL
    | D0 A B HprodR HdescR IHprodR
    | D0 E T tg E' Hch Hecons Hzero IHzero Hcons IHcons ]; intros d k.
  - (* ag_choice_nil *)
    apply (@ag_choice_nil (lift d k D0) (lift d k E) (lift d k T)).
    + exact (pruning_eval_lift d k _ _ Hnil).
    + exact (pruning_eval_lift d k _ _ Hecons).
  - (* ag_prod_left *)
    apply (@ag_prod_left (lift d k D0) (lift d k A) (lift d k B)).
    + exact (pruning_eval_lift d k _ _ HprodL).
    + exact (IHprodL d k).
  - (* ag_prod_right *)
    apply (@ag_prod_right (lift d k D0) (lift d k A) (lift d k B)).
    + exact (pruning_eval_lift d k _ _ HprodR).
    + exact (IHprodR d k).
  - (* ag_choice_cons *)
    apply (@ag_choice_cons (lift d k D0) (lift d k E) (lift d k T)
                           (lift d k tg) (lift d k E')).
    + exact (pruning_eval_lift d k _ _ Hch).
    + exact (pruning_eval_lift d k _ _ Hecons).
    + exact (IHzero d k).
    + rewrite <- (lift_lift_one_zero T d k). exact (IHcons d k).
Qed.


Lemma instance_dead_lift : forall D d k,
  instance_dead D -> instance_dead (lift d k D).
Proof.
  intros D d k [D0 [HD0 Hjoin]]. exists (lift d k D0).
  split; [apply pruning_against_lift; exact HD0|].
  rewrite !phi_erase_lift. apply cjoin_lift_parent; exact Hjoin.
Qed.

Lemma prune_lift_mut :
  (forall t u, prune_term t u -> forall d k,
    prune_term (lift d k t) (lift d k u)) /\
  (forall bs cs, prune_branches bs cs -> forall d k,
    prune_branches
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) cs)) /\
  (forall B L L', prune_labels B L L' -> forall d k,
    prune_labels (lift d k B) (lift d k L) (lift d k L')).
Proof.
  apply prune_mut_ind; intros; cbn;
    try solve [apply prune_term_refl]; try solve [constructor]; try solve [constructor; eauto];
    try solve [destruct (Nat.ltb n k); constructor].
  - apply pl_drop; [|auto].
    change (instance_dead (lift d k (TApp B c))).
    apply instance_dead_lift; assumption.
Qed.

Lemma prune_lift : forall t u, prune_term t u -> forall d k,
  prune_term (lift d k t) (lift d k u).
Proof. exact (proj1 prune_lift_mut). Qed.

Lemma prune_subst_var : forall n u u' k, prune_term u u' ->
  prune_term (subst u k (TVar n)) (subst u' k (TVar n)).
Proof.
  intros n u u' k H. cbn [subst].
  destruct (Nat.ltb n k); [constructor|].
  destruct (Nat.eqb n k); [apply prune_lift; exact H|constructor].
Qed.

Lemma prune_subst_mut :
  (forall t t', prune_term t t' -> forall u u' k, prune_term u u' ->
    prune_term (subst u k t) (subst u' k t')) /\
  (forall bs cs, prune_branches bs cs -> forall u u' k, prune_term u u' ->
    prune_branches
      (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
      (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) cs)) /\
  (forall B L L', prune_labels B L L' -> forall u u' k, prune_term u u' ->
    prune_labels (subst u k B) (subst u k L) (subst u' k L')).
Proof.
  apply prune_mut_ind; intros;
    try solve [apply prune_subst_var; assumption]; cbn;
    try solve [constructor]; try solve [constructor; eauto].
  - apply pl_drop; [|auto].
    change (instance_dead (subst u k (TApp B c))).
    apply instance_dead_subst; assumption.
Qed.

Lemma prune_subst : forall t t' u u' k,
  prune_term t t' -> prune_term u u' ->
  prune_term (subst u k t) (subst u' k t').
Proof. intros; eapply (proj1 prune_subst_mut); eassumption. Qed.

Print Assumptions prune_lift.
Print Assumptions prune_subst.
