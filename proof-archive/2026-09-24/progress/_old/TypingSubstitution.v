(* Structural substitution and weakening used by preservation. *)
Require Import Progress.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Definition subst_terms (u : term) (k : nat) (xs : list term) : list term :=
  map (subst u k) xs.

Definition lift_terms (d k : nat) (xs : list term) : list term :=
  map (lift d k) xs.

(* [Delta] lists declarations from the innermost one outward.  The removed
   declaration is therefore at cutoff [length Delta] in every judgment, while
   it occurs at successively smaller cutoffs in the declarations themselves. *)
Fixpoint subst_prefix (u : term) (Delta : ctx) : ctx :=
  match Delta with
  | [] => []
  | D :: Delta' => subst u (length Delta') D :: subst_prefix u Delta'
  end.

Lemma subst_prefix_length : forall u Delta,
    length (subst_prefix u Delta) = length Delta.
Proof. intros u Delta; induction Delta; cbn; congruence. Qed.

Lemma subst_prefix_cons : forall u D Delta,
    subst_prefix u (D :: Delta) =
      subst u (length Delta) D :: subst_prefix u Delta.
Proof. reflexivity. Qed.

Lemma nth_error_subst_prefix : forall u Delta n D,
    nth_error Delta n = Some D ->
    nth_error (subst_prefix u Delta) n =
      Some (subst u (length (skipn (S n) Delta)) D).
Proof.
  intros u Delta; induction Delta as [|D0 Delta IH]; intros n D Hnth.
  - destruct n; discriminate.
  - destruct n as [|n].
    + cbn in Hnth |- *. inversion Hnth; subst. reflexivity.
    + cbn in Hnth |- *. apply IH. exact Hnth.
Qed.

Definition subst_ctx (u : term) (Delta Gamma : ctx) : ctx :=
  subst_prefix u Delta ++ Gamma.

Definition subst_branches (u : term) (k : nat)
    (bs : list (term * term)) : list (term * term) :=
  map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs.

Lemma map_fst_subst_branches : forall u k bs,
    map fst (subst_branches u k bs) = subst_terms u k (map fst bs).
Proof.
  intros u k bs. unfold subst_branches, subst_terms.
  induction bs as [|[c b] bs IH]; cbn; [reflexivity|].
  f_equal. exact IH.
Qed.

Scheme wf_subst_ind := Induction for wf Sort Prop
with synth_subst_ind := Induction for synth Sort Prop
with check_subst_ind := Induction for check Sort Prop
with check_branches_subst_ind := Induction for check_branches Sort Prop
with sub_subst_ind := Induction for sub Sort Prop.

Combined Scheme typing_subst_ind
  from wf_subst_ind, synth_subst_ind, check_subst_ind,
       check_branches_subst_ind, sub_subst_ind.

Definition wf_subst_property (Gamma0 : ctx) (_ : wf Gamma0) : Prop :=
  forall D A G0 u,
    Gamma0 = D ++ A :: G0 ->
    check G0 u A ->
    wf (subst_ctx u D G0).

Definition synth_subst_property
    (Gamma0 : ctx) (t T : term) (_ : synth Gamma0 t T) : Prop :=
  forall D A G0 u,
    Gamma0 = D ++ A :: G0 ->
    check G0 u A ->
    check (subst_ctx u D G0)
      (subst u (length D) t) (subst u (length D) T).

Definition check_subst_property
    (Gamma0 : ctx) (t T : term) (_ : check Gamma0 t T) : Prop :=
  forall D A G0 u,
    Gamma0 = D ++ A :: G0 ->
    check G0 u A ->
    check (subst_ctx u D G0)
      (subst u (length D) t) (subst u (length D) T).

Definition branches_subst_property
    (Gamma0 : ctx) (Sf i E Q : term) (bs : list (term * term))
    (_ : check_branches Gamma0 Sf i E Q bs) : Prop :=
  forall D A G0 u,
    Gamma0 = D ++ A :: G0 ->
    check G0 u A ->
    check_branches (subst_ctx u D G0)
      (subst u (length D) Sf) (subst u (length D) i)
      (subst u (length D) E) (subst u (length D) Q)
      (subst_branches u (length D) bs).

Definition sub_subst_property
    (Gamma0 : ctx) (S T : term) (_ : sub Gamma0 S T) : Prop :=
  forall D A G0 u,
    Gamma0 = D ++ A :: G0 ->
    check G0 u A ->
    sub (subst_ctx u D G0)
      (subst u (length D) S) (subst u (length D) T).

(* The matching insertion operation.  This is the weakening companion used in
   the variable-equals-the-removed-binder case of substitution. *)
Fixpoint lift_prefix (Delta : ctx) : ctx :=
  match Delta with
  | [] => []
  | D :: Delta' => lift 1 (length Delta') D :: lift_prefix Delta'
  end.

Lemma lift_prefix_length : forall Delta,
    length (lift_prefix Delta) = length Delta.
Proof. induction Delta; cbn; congruence. Qed.

Definition weaken_ctx (Delta : ctx) (A : term) (Gamma : ctx) : ctx :=
  lift_prefix Delta ++ A :: Gamma.

Lemma nth_error_lift_prefix : forall Delta n D,
    nth_error Delta n = Some D ->
    nth_error (lift_prefix Delta) n =
      Some (lift 1 (length (skipn (S n) Delta)) D).
Proof.
  intros Delta; induction Delta as [|D0 Delta IH]; intros n D Hnth.
  - destruct n; discriminate.
  - destruct n as [|n].
    + cbn in Hnth |- *. inversion Hnth; subst. reflexivity.
    + cbn in Hnth |- *. apply IH. exact Hnth.
Qed.

Lemma synth_var_weaken : forall Delta Gamma A0 n X,
    wf (weaken_ctx Delta A0 Gamma) ->
    nth_error (Delta ++ Gamma) n = Some X ->
    synth (weaken_ctx Delta A0 Gamma) (lift 1 (length Delta) (TVar n))
      (lift 1 (length Delta) (lift (S n) 0 X)).
Proof.
  intros Delta Gamma A0 n X Hwf Hnth.
  destruct (Nat.lt_ge_cases n (length Delta)) as [Hlt|Hge].
  - assert (HD : nth_error Delta n = Some X).
    { rewrite nth_error_app1 in Hnth; auto. }
    set (r := length (skipn (S n) Delta)).
    assert (Hlen : length Delta = S n + r).
    { subst r. rewrite length_skipn. lia. }
    assert (Hlookup : nth_error (weaken_ctx Delta A0 Gamma) n =
        Some (lift 1 r X)).
    { unfold weaken_ctx. rewrite nth_error_app1.
      - apply nth_error_lift_prefix, HD.
      - rewrite lift_prefix_length. exact Hlt. }
    assert (Hterm : lift 1 (length Delta) (TVar n) = TVar n).
    { change ((if Nat.ltb n (length Delta) then TVar n else TVar (1+n)) = TVar n).
      assert (E : Nat.ltb n (length Delta) = true)
        by (apply Nat.ltb_lt; exact Hlt).
      rewrite E. reflexivity. }
    rewrite Hterm.
    replace (lift 1 (length Delta) (lift (S n) 0 X))
      with (lift (S n) 0 (lift 1 r X)).
    + exact (sy_var n Hwf Hlookup).
    + rewrite Hlen. symmetry. apply lift_lift_comm. lia.
  - set (m := n - length Delta).
    assert (Hn : n = length Delta + m) by (subst m; lia).
    assert (HG : nth_error Gamma m = Some X).
    { rewrite nth_error_app2 in Hnth; [|lia]. rewrite Hn in Hnth.
      replace (length Delta + m - length Delta) with m in Hnth by lia.
      exact Hnth. }
    assert (Hlookup : nth_error (weaken_ctx Delta A0 Gamma) (S n) = Some X).
    { unfold weaken_ctx. rewrite nth_error_app2.
      - rewrite lift_prefix_length.
        replace (S n - length Delta) with (S m) by (subst m; lia).
        cbn. exact HG.
      - rewrite lift_prefix_length. lia. }
    assert (Hterm : lift 1 (length Delta) (TVar n) = TVar (S n)).
    { change ((if Nat.ltb n (length Delta) then TVar n else TVar (1+n)) = TVar (S n)).
      assert (E : Nat.ltb n (length Delta) = false)
        by (apply Nat.ltb_ge; exact Hge).
      rewrite E. replace (1+n) with (S n) by lia. reflexivity. }
    rewrite Hterm.
    replace (lift 1 (length Delta) (lift (S n) 0 X))
      with (lift (S (S n)) 0 X).
    + exact (sy_var (S n) Hwf Hlookup).
    + replace (length Delta) with (0 + length Delta) by lia.
      rewrite lift_fuse; [f_equal; lia|lia].
Qed.

Definition lift_bs (D : ctx) (bs : list (term * term)) :=
  map (fun '(c,b) => (lift 1 (length D) c, lift 1 (S (length D)) b)) bs.

Lemma lift_Sig_typing : forall IT E d k,
  lift d k (Sig IT E) = Sig (lift d k IT) (lift d k E).
Proof.
  intros IT E d k. unfold Sig, Label. cbn [lift].
  rewrite !lift_lift_one_zero. reflexivity.
Qed.

Lemma map_fst_lift_bs : forall D bs,
  map fst (lift_bs D bs) = map (lift 1 (length D)) (map fst bs).
Proof. intros D bs. unfold lift_bs. induction bs as [|[c b] bs IH];
  cbn; [reflexivity|]. f_equal. exact IH. Qed.

Lemma lift_Carrier_typing : forall E Sf d k,
  lift d k (Carrier E Sf) = Carrier (lift d k E) (lift d k Sf).
Proof.
  intros E Sf d k. unfold Carrier, Full, branches.
  cbn [lift]. repeat rewrite lift_lift_one_zero. reflexivity.
Qed.

Definition wf_weaken_property (Gamma0 : ctx) (_ : wf Gamma0) : Prop :=
  forall D G0 A,
    Gamma0 = D ++ G0 ->
    wf (A :: G0) ->
    wf (weaken_ctx D A G0).

Definition synth_weaken_property
    (Gamma0 : ctx) (t T : term) (_ : synth Gamma0 t T) : Prop :=
  forall D G0 A,
    Gamma0 = D ++ G0 ->
    wf (A :: G0) ->
    synth (weaken_ctx D A G0)
      (lift 1 (length D) t) (lift 1 (length D) T).

Definition check_weaken_property
    (Gamma0 : ctx) (t T : term) (_ : check Gamma0 t T) : Prop :=
  forall D G0 A,
    Gamma0 = D ++ G0 ->
    wf (A :: G0) ->
    check (weaken_ctx D A G0)
      (lift 1 (length D) t) (lift 1 (length D) T).

Definition branches_weaken_property
    (Gamma0 : ctx) (Sf i E Q : term) (bs : list (term * term))
    (_ : check_branches Gamma0 Sf i E Q bs) : Prop :=
  forall D G0 A,
    Gamma0 = D ++ G0 ->
    wf (A :: G0) ->
    check_branches (weaken_ctx D A G0)
      (lift 1 (length D) Sf) (lift 1 (length D) i)
      (lift 1 (length D) E) (lift 1 (length D) Q)
      (lift_bs D bs).

Definition sub_weaken_property
    (Gamma0 : ctx) (S T : term) (_ : sub Gamma0 S T) : Prop :=
  forall D G0 A,
    Gamma0 = D ++ G0 ->
    wf (A :: G0) ->
    sub (weaken_ctx D A G0)
      (lift 1 (length D) S) (lift 1 (length D) T).

Theorem step_lift_typing : forall t t', step t t' -> forall d k,
    step (lift d k t) (lift d k t').
Proof.
  intros t t' H; induction H; intros d kk;
    try solve [cbn; constructor; eauto];
    try solve [cbn;
      repeat rewrite (lift_lift_one_zero _ d kk);
      repeat rewrite (lift_lift_one_one _ d kk);
      repeat rewrite (lift_lift_two_zero _ d kk); constructor];
    try solve [cbn; rewrite lift_subst_zero_comm; constructor].
  - cbn.
    rewrite (lift_lift_one_zero E d kk).
    rewrite (lift_lift_one_one (lift 1 0 P) d kk).
    rewrite (lift_lift_one_zero P d kk).
    apply st_epi_cons.
  - cbn. rewrite lift_subst_zero_comm.
    eapply st_case.
    + eapply nth_error_lift_branches; exact H.
    + rewrite (enum_pos_lift_id c n H0 d kk). exact H0.
    + rewrite (enum_pos_lift_id a n H1 d kk). exact H1.
    + intros j cj bj Hj Hnthj. rewrite nth_error_map in Hnthj.
      destruct (nth_error bs j) as [[cj0 bj0]|] eqn:Horig;
        cbn in Hnthj; [|discriminate].
      inversion Hnthj; subst.
      destruct (H2 j cj0 bj0 Hj Horig) as [nj [Hp Hne]].
      exists nj. split.
      * rewrite (enum_pos_lift_id cj0 nj Hp d kk). exact Hp.
      * exact Hne.
  - cbn. rewrite !map_app. cbn. constructor; eauto.
Qed.

Lemma spine_phi_lift_typing : forall Sf i Phi Psi,
    spine_phi Sf i Phi Psi -> forall d k,
    spine_phi (lift d k Sf) (lift d k i) (lift d k Phi) (lift d k Psi).
Proof.
  intros Sf i Phi Psi H; induction H; intros d k.
  - apply sph_nil. exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
  - eapply sph_keep.
    + exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
    + exact (IHspine_phi d k).
  - eapply sph_drop.
    + exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
    + exact (_parent_instance_pruning.pruning_against_lift _ H0 d k).
    + exact (IHspine_phi d k).
  - apply sph_tail.
Qed.

Lemma lift_phi_family_typing : forall Sf d k,
    lift d k (TLam (branches (TApp (lift 1 0 Sf) (TVar 0)))) =
    TLam (branches (TApp (lift 1 0 (lift d k Sf)) (TVar 0))).
Proof.
  intros Sf d k.
  change
    ((TLam (TFst (TApp (lift d (S k) (lift 1 0 Sf)) (TVar 0)))) =
     (TLam (TFst (TApp (lift 1 0 (lift d k Sf)) (TVar 0))))).
  rewrite lift_lift_one_zero. reflexivity.
Qed.

Theorem conv_lift_typing : forall t t', conv t t' -> forall d k,
    conv (lift d k t) (lift d k t').
Proof.
  intros t t' H; induction H; intros d k; cbn.
  - apply cv_step. exact (step_lift_typing _ _ H d k).
  - apply cv_refl.
  - apply cv_sym. exact (IHconv d k).
  - eapply cv_trans; [exact (IHconv1 d k) | exact (IHconv2 d k)].
  - rewrite lift_lift_one_zero. apply cv_eta.
  - apply cv_pi; auto.
  - apply cv_lam; auto.
  - apply cv_app; auto.
  - apply cv_sigma; auto.
  - apply cv_pair; auto.
  - apply cv_fst; auto.
  - apply cv_snd; auto.
  - apply cv_conse; auto.
  - apply cv_enumt; auto.
  - apply cv_esucc; auto.
  - apply cv_epi; auto.
  - apply cv_switch; auto.
  - apply cv_idesc; auto.
  - apply cv_ivar; auto.
  - apply cv_iprod; auto.
  - apply cv_ipi; auto.
  - apply cv_isig; auto.
  - apply cv_ichoice; auto.
  - apply cv_interp; auto.
  - apply cv_mui; auto.
  - apply cv_mus; auto.
  - apply cv_in; auto.
  - apply cv_ind; auto.
  - apply cv_iall; auto.
  - apply cv_hyps; auto.
  - apply cv_list; auto.
  - apply cv_lnil; auto.
  - apply cv_lcons; auto.
  - apply cv_case; auto.
  - rewrite !map_app; cbn. apply cv_case_br; auto.
Qed.

Lemma subst_eta_shape_typing : forall f u k,
    subst u k (TLam (TApp (lift 1 0 f) (TVar 0))) =
    TLam (TApp (lift 1 0 (subst u k f)) (TVar 0)).
Proof.
  intros f u k; cbn. rewrite subst_lift_one_zero. reflexivity.
Qed.

Lemma subst_phi_family_typing : forall Sf u k,
    subst u k (TLam (branches (TApp (lift 1 0 Sf) (TVar 0)))) =
    TLam (branches (TApp (lift 1 0 (subst u k Sf)) (TVar 0))).
Proof.
  intros Sf u k.
  change
    ((TLam (TFst (TApp (subst u (S k) (lift 1 0 Sf)) (TVar 0)))) =
     (TLam (TFst (TApp (lift 1 0 (subst u k Sf)) (TVar 0))))).
  rewrite subst_lift_one_zero. reflexivity.
Qed.

Lemma spine_phi_subst_same : forall Sf i Phi Psi,
    spine_phi Sf i Phi Psi -> forall u k,
    spine_phi (subst u k Sf) (subst u k i)
      (subst u k Phi) (subst u k Psi).
Proof.
  intros Sf i Phi Psi H; induction H; intros u k.
  - cbn. apply sph_nil.
    exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
  - cbn. eapply sph_keep.
    + exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
    + exact (IHspine_phi u k).
  - cbn [branches]. eapply sph_drop.
    + exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
    + exact (_parent_instance_pruning.pruning_against_subst _ H0 u k).
    + exact (IHspine_phi u k).
  - apply sph_tail.
Qed.

Theorem conv_subst_same : forall t t',
    conv t t' -> forall u k, conv (subst u k t) (subst u k t').
Proof.
  intros t t' H; induction H; intros z k; cbn.
  - apply cv_step. exact (_parent_instance_pruning.pruning_step_subst _ _ H z k).
  - apply cv_refl.
  - apply cv_sym. exact (IHconv z k).
  - eapply cv_trans; [exact (IHconv1 z k) | exact (IHconv2 z k)].
  - rewrite subst_lift_one_zero. apply cv_eta.
  - apply cv_pi; auto.
  - apply cv_lam; auto.
  - apply cv_app; auto.
  - apply cv_sigma; auto.
  - apply cv_pair; auto.
  - apply cv_fst; auto.
  - apply cv_snd; auto.
  - apply cv_conse; auto.
  - apply cv_enumt; auto.
  - apply cv_esucc; auto.
  - apply cv_epi; auto.
  - apply cv_switch; auto.
  - apply cv_idesc; auto.
  - apply cv_ivar; auto.
  - apply cv_iprod; auto.
  - apply cv_ipi; auto.
  - apply cv_isig; auto.
  - apply cv_ichoice; auto.
  - apply cv_interp; auto.
  - apply cv_mui; auto.
  - apply cv_mus; auto.
  - apply cv_in; auto.
  - apply cv_ind; auto.
  - apply cv_iall; auto.
  - apply cv_hyps; auto.
  - apply cv_list; auto.
  - apply cv_lnil; auto.
  - apply cv_lcons; auto.
  - apply cv_case; auto.
  - rewrite !map_app; cbn. apply cv_case_br; auto.
Qed.

Lemma spine_mem_subst : forall c Phi,
    spine_mem c Phi -> forall u k,
    spine_mem (subst u k c) (subst u k Phi).
Proof.
  intros c Phi H; induction H; intros u k.
  - eapply sm_here.
    + exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
    + exact (conv_subst_same _ _ H0 u k).
  - eapply sm_there.
    + exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
    + exact (IHspine_mem u k).
Qed.

Lemma eval_subst_typing : forall t v,
    eval t v -> forall u k, eval (subst u k t) (subst u k v).
Proof. exact _parent_instance_pruning.pruning_eval_subst. Qed.

Lemma spine_tail_subst : forall Phi Psi,
    spine_tail Phi Psi -> forall u k,
    spine_tail (subst u k Phi) (subst u k Psi).
Proof.
  intros Phi Psi H; induction H; intros u k.
  - apply stl_here.
    exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
  - eapply stl_there.
    + exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
    + exact (IHspine_tail u k).
Qed.

Lemma spine_incl_subst : forall Phi Psi,
    spine_incl Phi Psi -> forall u k,
    spine_incl (subst u k Phi) (subst u k Psi).
Proof.
  intros Phi Psi H; induction H; intros u k.
  - eapply si_nil.
    exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
  - eapply si_cons.
    + exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
    + exact (spine_mem_subst _ _ H0 u k).
    + exact (IHspine_incl u k).
  - apply si_tail. exact (spine_tail_subst _ _ H u k).
Qed.

Lemma exists_conv_subst : forall c cs,
    Exists (fun c' => conv c c') cs -> forall u k,
    Exists (fun c' => conv (subst u k c) c') (subst_terms u k cs).
Proof.
  intros c cs H; induction H; intros u k; cbn.
  - constructor. exact (conv_subst_same _ _ H u k).
  - constructor 2. exact (IHExists u k).
Qed.

Lemma covers_subst : forall cs Phi,
    covers cs Phi -> forall u k,
    covers (subst_terms u k cs) (subst u k Phi).
Proof.
  intros cs Phi H; induction H; intros u k.
  - eapply cov_nil.
    exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
  - eapply cov_cons.
    + exact (_parent_instance_pruning.pruning_eval_subst _ _ H u k).
    + exact (exists_conv_subst _ _ H0 u k).
    + exact (IHcovers u k).
Qed.

Lemma distinct_all_positions : forall cs, distinct cs ->
    Forall (fun c => exists n, enum_pos c n) cs.
Proof.
  intros cs H; induction H.
  - constructor.
  - constructor; [now exists n | exact IHdistinct].
Qed.

Lemma subst_terms_canonical_id : forall cs,
    Forall (fun c => exists n, enum_pos c n) cs -> forall u k,
    subst_terms u k cs = cs.
Proof.
  intros cs H; induction H; intros u k; cbn; [reflexivity |].
  destruct H as [n Hpos].
  rewrite (enum_pos_subst_id x n Hpos u k).
  f_equal. exact (IHForall u k).
Qed.

Lemma distinct_subst : forall cs,
    distinct cs -> forall u k, distinct (subst_terms u k cs).
Proof.
  intros cs H u k.
  rewrite (subst_terms_canonical_id cs (distinct_all_positions cs H) u k).
  exact H.
Qed.

Lemma spine_mem_lift : forall c Phi,
    spine_mem c Phi -> forall d k,
    spine_mem (lift d k c) (lift d k Phi).
Proof.
  intros c Phi H; induction H; intros d k.
  - eapply sm_here.
    + exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
    + apply conv_lift_typing. exact H0.
  - eapply sm_there.
    + exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
    + exact (IHspine_mem d k).
Qed.

Lemma spine_tail_lift : forall Phi Psi,
    spine_tail Phi Psi -> forall d k,
    spine_tail (lift d k Phi) (lift d k Psi).
Proof.
  intros Phi Psi H; induction H; intros d k.
  - apply stl_here.
    exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
  - eapply stl_there.
    + exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
    + exact (IHspine_tail d k).
Qed.

Lemma spine_incl_lift : forall Phi Psi,
    spine_incl Phi Psi -> forall d k,
    spine_incl (lift d k Phi) (lift d k Psi).
Proof.
  intros Phi Psi H; induction H; intros d k.
  - eapply si_nil.
    exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
  - eapply si_cons.
    + exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
    + exact (spine_mem_lift _ _ H0 d k).
    + exact (IHspine_incl d k).
  - apply si_tail. exact (spine_tail_lift _ _ H d k).
Qed.

Lemma exists_conv_lift : forall c cs,
    Exists (fun c' => conv c c') cs -> forall d k,
    Exists (fun c' => conv (lift d k c) c') (lift_terms d k cs).
Proof.
  intros c cs H; induction H; intros d k; cbn.
  - constructor. apply conv_lift_typing. exact H.
  - constructor 2. exact (IHExists d k).
Qed.

Lemma covers_lift : forall cs Phi,
    covers cs Phi -> forall d k,
    covers (lift_terms d k cs) (lift d k Phi).
Proof.
  intros cs Phi H; induction H; intros d k.
  - eapply cov_nil.
    exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
  - eapply cov_cons.
    + exact (_parent_instance_pruning.pruning_eval_lift d k _ _ H).
    + exact (exists_conv_lift _ _ H0 d k).
    + exact (IHcovers d k).
Qed.

Lemma distinct_lift : forall cs,
    distinct cs -> forall d k, distinct (lift_terms d k cs).
Proof.
  intros cs H d k.
  unfold lift_terms.
  erewrite map_ext_in with (g := fun c => c).
  - rewrite map_id. exact H.
  - intros c Hin.
    pose proof (distinct_all_positions cs H) as Hall.
    apply Forall_forall with (x := c) in Hall; [|exact Hin].
    destruct Hall as [n Hpos]. exact (enum_pos_lift_id c n Hpos d k).
Qed.

Theorem typing_weaken_mutual :
  (forall Gamma (H : wf Gamma), wf_weaken_property Gamma H) /\
  (forall Gamma t T (H : synth Gamma t T),
      synth_weaken_property Gamma t T H) /\
  (forall Gamma t T (H : check Gamma t T),
      check_weaken_property Gamma t T H) /\
  (forall Gamma Sf i E Q bs
      (H : check_branches Gamma Sf i E Q bs),
      branches_weaken_property Gamma Sf i E Q bs H) /\
  (forall Gamma S T (H : sub Gamma S T),
      sub_weaken_property Gamma S T H).
Proof.
  apply typing_subst_ind; unfold wf_weaken_property,
    synth_weaken_property, check_weaken_property,
    branches_weaken_property, sub_weaken_property;
    intros; subst; cbn [weaken_ctx lift_prefix lift_bs] in *.
  - destruct D as [|X D']; cbn in H |- *.
    + inversion H; subst. exact H0.
    + discriminate.
  - destruct D as [|X D']; cbn in H1 |- *.
    + inversion H1; subst. exact H2.
    + inversion H1; subst X.
      eapply wf_cons with (k := k).
      * eapply H; [exact H5 | exact H2].
      * eapply H0; [exact H5 | exact H2].
  - eapply synth_var_weaken.
    + eapply H; [reflexivity | exact H1].
    + exact e.
  - cbn. apply sy_sort. eapply H; [reflexivity | exact H1].
  - cbn. apply sy_pi.
    + eapply H; [reflexivity | exact H2].
    + eapply H0 with (D := A :: D); [reflexivity | exact H2].
  - cbn. apply sy_sigma.
    + eapply H; [reflexivity | exact H2].
    + eapply H0 with (D := A :: D); [reflexivity | exact H2].
  - rewrite lift_subst_zero_comm. cbn. eapply sy_app.
    + eapply H; [reflexivity | exact H3].
    + eapply H0; [reflexivity | exact H3].
    + exact (_parent_instance_pruning.pruning_eval_lift 1 (length D) _ _ e).
    + eapply H1; [reflexivity | exact H3].
  - cbn. eapply sy_fst.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
    + exact (_parent_instance_pruning.pruning_eval_lift 1 (length D) _ _ e).
  - rewrite lift_subst_zero_comm. cbn. eapply sy_snd.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
    + exact (_parent_instance_pruning.pruning_eval_lift 1 (length D) _ _ e).
  - change (synth (weaken_ctx D A G0) TUnitT (TSort k)).
    apply sy_unitT. eapply H; [reflexivity | exact H1].
  - change (synth (weaken_ctx D A G0) TUnit TUnitT).
    apply sy_unit. eapply H; [reflexivity | exact H1].
  - change (synth (weaken_ctx D A G0) TUId (TSort 0)).
    apply sy_uid. eapply H; [reflexivity | exact H1].
  - change (synth (weaken_ctx D A G0) TEnumU (TSort 0)).
    apply sy_enumu. eapply H; [reflexivity | exact H1].
  - change (synth (weaken_ctx D A G0) (TTag s) TUId).
    apply sy_tag. eapply H; [reflexivity | exact H1].
  - change (synth (weaken_ctx D A G0) TNilE TEnumU).
    apply sy_nile. eapply H; [reflexivity | exact H1].
  - cbn. apply sy_conse.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
  - cbn. apply sy_enumt. eapply H; [reflexivity | exact H1].
  - cbn. apply sy_epi.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
  - cbn. apply sy_switch with (k := k).
    + eapply H; [reflexivity | exact H4].
    + eapply H0; [reflexivity | exact H4].
    + eapply H1; [reflexivity | exact H4].
    + eapply H2; [reflexivity | exact H4].
  - cbn. apply sy_idesc. eapply H; [reflexivity | exact H1].
  - cbn. apply sy_interp with (IT := lift 1 (length D0) IT).
    + eapply H; [reflexivity | exact H3].
    + eapply H0; [reflexivity | exact H3].
    + eapply H1; [reflexivity | exact H3].
  - cbn. apply sy_mui with (IT := lift 1 (length D) IT).
    + eapply H; [reflexivity | exact H2].
    + specialize (H0 D G0 A eq_refl H2). cbn in H0.
      rewrite lift_lift_one_zero in H0. exact H0.
  - cbn. apply sy_iall with (IT := lift 1 (length D0) IT).
    + eapply H; [reflexivity | exact H5].
    + eapply H0; [reflexivity | exact H5].
    + eapply H1; [reflexivity | exact H5].
    + eapply H2; [reflexivity | exact H5].
    + specialize (H3 D0 G0 A eq_refl H5). cbn in H3.
      rewrite lift_lift_one_zero in H3. exact H3.
  - cbn. apply sy_hyps with (IT := lift 1 (length D0) IT).
    + eapply H; [reflexivity | exact H6].
    + eapply H0; [reflexivity | exact H6].
    + eapply H1; [reflexivity | exact H6].
    + specialize (H2 D0 G0 A eq_refl H6). cbn in H2.
      rewrite lift_lift_one_zero in H2. exact H2.
    + specialize (H3 D0 G0 A eq_refl H6). cbn in H3.
      rewrite lift_lift_one_zero, lift_lift_two_zero in H3. exact H3.
    + eapply H4; [reflexivity | exact H6].
  - cbn. apply sy_ind with (IT := lift 1 (length D) IT).
    + eapply H; [reflexivity | exact H6].
    + specialize (H0 D G0 A eq_refl H6). cbn in H0.
      rewrite lift_lift_one_zero in H0. exact H0.
    + specialize (H1 D G0 A eq_refl H6). cbn in H1.
      rewrite lift_lift_one_zero in H1. exact H1.
    + specialize (H2 D G0 A eq_refl H6). cbn in H2.
      repeat rewrite lift_lift_one_zero in H2.
      repeat rewrite lift_lift_two_zero in H2.
      replace (S (S (S (length D)))) with (3 + length D) in H2 by lia.
      rewrite (lift_lift_comm P 1 3 0 (length D)) in H2 by lia.
      exact H2.
    + eapply H3; [reflexivity | exact H6].
    + eapply H4; [reflexivity | exact H6].
  - cbn. apply sy_mus with (IT := lift 1 (length D) IT)
      (E := lift 1 (length D) E).
    + eapply H; [reflexivity | exact H3].
    + eapply H0; [reflexivity | exact H3].
    + specialize (H1 D G0 A eq_refl H3).
      assert (Ety :
        lift 1 (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (lift 1 (length D) IT)
          (Sig (lift 1 0 (lift 1 (length D) IT))
               (lift 1 0 (lift 1 (length D) E)))).
      { change
          (TPi (lift 1 (length D) IT)
             (lift 1 (S (length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
           TPi (lift 1 (length D) IT)
             (Sig (lift 1 0 (lift 1 (length D) IT))
                  (lift 1 0 (lift 1 (length D) E)))).
        rewrite lift_Sig_typing, !lift_lift_one_zero. reflexivity. }
      rewrite <- Ety. exact H1.
  - cbn. eapply sy_case with
      (Sf := lift 1 (length D) Sf) (i := lift 1 (length D) i)
      (IT := lift 1 (length D) IT) (E := lift 1 (length D) E)
      (k := k) (Phi := lift 1 (length D) Phi).
    + eapply H; [reflexivity | exact H7].
    + eapply H0; [reflexivity | exact H7].
    + eapply H1; [reflexivity | exact H7].
    + specialize (H2 D G0 A eq_refl H7).
      assert (Ety :
        lift 1 (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (lift 1 (length D) IT)
          (Sig (lift 1 0 (lift 1 (length D) IT))
               (lift 1 0 (lift 1 (length D) E)))).
      { change
          (TPi (lift 1 (length D) IT)
             (lift 1 (S (length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
           TPi (lift 1 (length D) IT)
             (Sig (lift 1 0 (lift 1 (length D) IT))
                  (lift 1 0 (lift 1 (length D) E)))).
        rewrite lift_Sig_typing, !lift_lift_one_zero. reflexivity. }
      rewrite <- Ety. exact H2.
    + eapply H3; [reflexivity | exact H7].
    + eapply H4; [reflexivity | exact H7].
    + change (distinct (map fst (lift_bs D bs))).
      rewrite map_fst_lift_bs. exact (distinct_lift _ d 1 (length D)).
    + exact (_parent_instance_pruning.pruning_eval_lift 1 (length D) _ _ e).
    + change (covers (map fst (lift_bs D bs)) (lift 1 (length D) Phi)).
      rewrite map_fst_lift_bs. exact (covers_lift _ _ c5 1 (length D)).
    + eapply H5; [reflexivity | exact H7].
  - cbn. apply sy_list. eapply H; [reflexivity | exact H1].
  - cbn. apply sy_lnil. eapply H; [reflexivity | exact H1].
  - cbn. apply sy_lcons.
    + eapply H; [reflexivity | exact H3].
    + eapply H0; [reflexivity | exact H3].
    + eapply H1; [reflexivity | exact H3].
  - eapply ch_conv.
    + eapply H; [reflexivity | exact H1].
    + exact (conv_lift_typing _ _ c 1 (length D)).
  - eapply ch_sub.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
  - eapply ch_expand.
    + exact (conv_lift_typing _ _ c 1 (length D)).
    + eapply H; [reflexivity | exact H1].
  - cbn. apply ch_lam.
    eapply H with (D := A :: D); [reflexivity | exact H1].
  - cbn. apply ch_pair.
    + eapply H; [reflexivity | exact H2].
    + specialize (H0 D G0 A0 eq_refl H2).
      rewrite lift_subst_zero_comm in H0. exact H0.
  - rewrite lift_subst_zero_comm. cbn. eapply ch_app.
    + eapply H; [reflexivity | exact H3].
    + eapply H0; [reflexivity | exact H3].
    + eapply H1; [reflexivity | exact H3].
  - cbn. eapply ch_fst.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
  - rewrite lift_subst_zero_comm. cbn. eapply ch_snd.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
  - cbn. apply ch_ezero.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
  - cbn. apply ch_esucc.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
  - cbn. apply ch_ivar. eapply H; [reflexivity | exact H1].
  - cbn. apply ch_i1. eapply H; [reflexivity | exact H1].
  - cbn. apply ch_iprod.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
  - cbn. apply ch_ipi.
    + eapply H; [reflexivity | exact H2].
    + specialize (H0 D G0 A eq_refl H2). cbn in H0.
      rewrite lift_lift_one_zero in H0. exact H0.
  - cbn. apply ch_isig.
    + eapply H; [reflexivity | exact H2].
    + specialize (H0 D G0 A eq_refl H2). cbn in H0.
      rewrite lift_lift_one_zero in H0. exact H0.
  - cbn. apply ch_ichoice.
    + eapply H; [reflexivity | exact H2].
    + specialize (H0 D G0 A eq_refl H2). cbn in H0.
      rewrite lift_lift_one_zero in H0. exact H0.
  - cbn. apply ch_in_mui with (IT := lift 1 (length D) IT).
    + eapply H; [reflexivity | exact H4].
    + specialize (H0 D G0 A eq_refl H4). cbn in H0.
      rewrite lift_lift_one_zero in H0. exact H0.
    + eapply H1; [reflexivity | exact H4].
    + eapply H2; [reflexivity | exact H4].
  - cbn. eapply ch_in_sig with
      (IT := lift 1 (length D) IT) (E := lift 1 (length D) E)
      (Phi := lift 1 (length D) Phi).
    + eapply H; [reflexivity | exact H6].
    + eapply H0; [reflexivity | exact H6].
    + specialize (H1 D G0 A eq_refl H6).
      assert (Ety :
        lift 1 (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (lift 1 (length D) IT)
          (Sig (lift 1 0 (lift 1 (length D) IT))
               (lift 1 0 (lift 1 (length D) E)))).
      { change
          (TPi (lift 1 (length D) IT)
             (lift 1 (S (length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
           TPi (lift 1 (length D) IT)
             (Sig (lift 1 0 (lift 1 (length D) IT))
                  (lift 1 0 (lift 1 (length D) E)))).
        rewrite lift_Sig_typing, !lift_lift_one_zero. reflexivity. }
      rewrite <- Ety. exact H1.
    + eapply H2; [reflexivity | exact H6].
    + eapply H3; [reflexivity | exact H6].
    + exact (_parent_instance_pruning.pruning_eval_lift 1 (length D) _ _ e).
    + exact (spine_mem_lift _ _ s 1 (length D)).
    + specialize (H4 D G0 A eq_refl H6).
      assert (Epayload :
        lift 1 (length D)
          (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) =
        TInterp
          (TApp (branches (TApp (lift 1 (length D) Sf)
                                  (lift 1 (length D) i)))
                (lift 1 (length D) c))
          (Carrier (lift 1 (length D) E) (lift 1 (length D) Sf))).
      { change
          (TInterp
             (TApp (branches (TApp (lift 1 (length D) Sf)
                                     (lift 1 (length D) i)))
                   (lift 1 (length D) c))
             (lift 1 (length D) (Carrier E Sf)) =
           TInterp
             (TApp (branches (TApp (lift 1 (length D) Sf)
                                     (lift 1 (length D) i)))
                   (lift 1 (length D) c))
             (Carrier (lift 1 (length D) E) (lift 1 (length D) Sf))).
        rewrite lift_Carrier_typing. reflexivity. }
      rewrite <- Epayload. exact H4.
  - cbn [lift_bs]. constructor.
  - cbn [lift_bs]. apply cb_cons.
    + eapply H; [reflexivity | exact H3].
    + specialize (H0
        (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf) :: D)
        G0 A eq_refl H3).
      cbn [length weaken_ctx lift_prefix] in H0.
      rewrite lift_lift_one_zero in H0.
      change
        (check
          (lift 1 (length D)
             (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf))
           :: weaken_ctx D A G0)
          (lift 1 (S (length D)) b)
          (lift 1 0 (lift 1 (length D) Q))) in H0.
      rewrite <- lift_Carrier_typing.
      exact H0.
    + eapply H1; [reflexivity | exact H3].
  all: try solve [cbn [lift]; constructor; eapply H; [reflexivity | exact H1]].
  all: try solve [cbn [lift]; econstructor; eauto 8 using
    conv_lift_typing, _parent_instance_pruning.pruning_eval_lift, spine_mem_lift, spine_incl_lift,
    covers_lift, distinct_lift].
  - apply su_conv. exact (conv_lift_typing _ _ c 1 (length D)).
  - eapply su_trans.
    + eapply H; [reflexivity | exact H2].
    + eapply H0; [reflexivity | exact H2].
  - cbn. apply su_sort. exact l.
  - cbn. apply su_pi.
    + eapply H; [reflexivity | exact H2].
    + eapply H0 with (D := A' :: D); [reflexivity | exact H2].
  - change
      (sub (weaken_ctx D A G0)
        (TApp (SigMu (lift 1 (length D) E) (lift 1 (length D) Sf))
          (lift 1 (length D) i))
        (TApp (lift 1 (length D) (Carrier E Sf)) (lift 1 (length D) i))).
    rewrite lift_Carrier_typing.
    eapply su_forget with
      (IT := lift 1 (length D) IT) (E := lift 1 (length D) E).
    + eapply H; [reflexivity | exact H4].
    + eapply H0; [reflexivity | exact H4].
    + specialize (H1 D G0 A eq_refl H4).
      assert (Ety :
        lift 1 (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (lift 1 (length D) IT)
          (Sig (lift 1 0 (lift 1 (length D) IT))
               (lift 1 0 (lift 1 (length D) E)))).
      { change
          (TPi (lift 1 (length D) IT)
             (lift 1 (S (length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
           TPi (lift 1 (length D) IT)
             (Sig (lift 1 0 (lift 1 (length D) IT))
                  (lift 1 0 (lift 1 (length D) E)))).
        rewrite lift_Sig_typing, !lift_lift_one_zero. reflexivity. }
      rewrite <- Ety. exact H1.
    + eapply H2; [reflexivity | exact H4].
  - cbn. eapply su_sig with
      (IT := lift 1 (length D) IT) (E := lift 1 (length D) E)
      (Phi1 := lift 1 (length D) Phi1) (Phi2 := lift 1 (length D) Phi2).
    + eapply H; [reflexivity | exact H5].
    + eapply H0; [reflexivity | exact H5].
    + specialize (H1 D G0 A eq_refl H5).
      assert (Ety :
        lift 1 (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (lift 1 (length D) IT)
          (Sig (lift 1 0 (lift 1 (length D) IT))
               (lift 1 0 (lift 1 (length D) E)))).
      { change
          (TPi (lift 1 (length D) IT)
             (lift 1 (S (length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
           TPi (lift 1 (length D) IT)
             (Sig (lift 1 0 (lift 1 (length D) IT))
                  (lift 1 0 (lift 1 (length D) E)))).
        rewrite lift_Sig_typing, !lift_lift_one_zero. reflexivity. }
      rewrite <- Ety. exact H1.
    + specialize (H2 D G0 A eq_refl H5).
      assert (Ety2 :
        lift 1 (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (lift 1 (length D) IT)
          (Sig (lift 1 0 (lift 1 (length D) IT))
               (lift 1 0 (lift 1 (length D) E)))).
      { change
          (TPi (lift 1 (length D) IT)
             (lift 1 (S (length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
           TPi (lift 1 (length D) IT)
             (Sig (lift 1 0 (lift 1 (length D) IT))
                  (lift 1 0 (lift 1 (length D) E)))).
        rewrite lift_Sig_typing, !lift_lift_one_zero. reflexivity. }
      rewrite <- Ety2. exact H2.
    + specialize (conv_lift_typing _ _ c3 1 (length D)) as HC.
      cbn in HC. rewrite !lift_lift_one_zero in HC. exact HC.
    + exact (_parent_instance_pruning.pruning_eval_lift 1 (length D) _ _ e).
    + exact (_parent_instance_pruning.pruning_eval_lift 1 (length D) _ _ e0).
    + exact (spine_incl_lift _ _ s 1 (length D)).
    + eapply H3; [reflexivity | exact H5].
Qed.

Theorem check_weaken : forall D G A t T,
    check (D ++ G) t T -> wf (A :: G) ->
    check (weaken_ctx D A G)
      (lift 1 (length D) t) (lift 1 (length D) T).
Proof.
  intros D G A t T Hck Hwf.
  destruct typing_weaken_mutual as [_ [_ [HC _]]].
  eapply (HC _ _ _ Hck D G A); [reflexivity | exact Hwf].
Qed.

Theorem check_weaken0 : forall G A t T,
    check G t T -> wf (A :: G) ->
    check (A :: G) (lift 1 0 t) (lift 1 0 T).
Proof.
  intros G A t T Hck Hwf.
  exact (check_weaken [] G A t T Hck Hwf).
Qed.

Lemma wf_app_tail : forall D G, wf (D ++ G) -> wf G.
Proof.
  induction D as [|X D IH]; intros G Hwf; cbn in Hwf; [exact Hwf|].
  inversion Hwf; subst. eapply IH. exact H1.
Qed.

Theorem check_lift_into : forall D G u A,
    check G u A -> wf (D ++ G) ->
    check (D ++ G) (lift (length D) 0 u) (lift (length D) 0 A).
Proof.
  induction D as [|X D IH]; intros G u A Hck Hwf; cbn in *.
  - rewrite !_tmp_commute.lift_zero_id_local. exact Hck.
  - inversion Hwf; subst.
    specialize (IH G u A Hck H1).
    pose proof (check_weaken0 (D ++ G) X
      (lift (length D) 0 u) (lift (length D) 0 A) IH Hwf) as HW.
    replace (S (length D)) with (1 + length D) by lia.
    rewrite <- (lift_fuse u 1 (length D) 0 0) by lia.
    rewrite <- (lift_fuse A 1 (length D) 0 0) by lia.
    exact HW.
Qed.

Lemma subst_var_lt_typing : forall n k u, n < k ->
    subst u k (TVar n) = TVar n.
Proof.
  intros n k u H. change ((if n <? k then TVar n else
    if n =? k then lift k 0 u else TVar (pred n)) = TVar n).
  destruct (n <? k) eqn:E; [reflexivity|].
  apply Nat.ltb_ge in E; lia.
Qed.

Lemma subst_var_eq_typing : forall k u,
    subst u k (TVar k) = lift k 0 u.
Proof.
  intros k u. change ((if k <? k then TVar k else
    if k =? k then lift k 0 u else TVar (pred k)) = lift k 0 u).
  destruct (k <? k) eqn:E; [apply Nat.ltb_lt in E; lia|].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma subst_var_gt_typing : forall n k u, k < n ->
    subst u k (TVar n) = TVar (pred n).
Proof.
  intros n k u H. change ((if n <? k then TVar n else
    if n =? k then lift k 0 u else TVar (pred n)) = TVar (pred n)).
  destruct (n <? k) eqn:E; [apply Nat.ltb_lt in E; lia|].
  destruct (n =? k) eqn:E2;
    [apply Nat.eqb_eq in E2; lia|reflexivity].
Qed.

Lemma subst_lift_delete : forall t u k n, k <= n ->
    subst u k (lift (S n) 0 t) = lift n 0 t.
Proof.
  intros t u k n Hkn. replace (S n) with (1 + n) by lia.
  rewrite <- (lift_fuse t 1 n 0 k) by lia.
  apply subst_lift_cancel.
Qed.

Lemma synth_var_subst : forall D A0 G u n X,
    wf (subst_ctx u D G) -> check G u A0 ->
    nth_error (D ++ A0 :: G) n = Some X ->
    check (subst_ctx u D G)
      (subst u (length D) (TVar n))
      (subst u (length D) (lift (S n) 0 X)).
Proof.
  intros D A0 G u n X Hwf Hu Hnth.
  unfold subst_ctx in *.
  destruct (Nat.lt_trichotomy n (length D)) as [Hlt|[Heq|Hgt]].
  - assert (HD : nth_error D n = Some X).
    { rewrite nth_error_app1 in Hnth; auto. }
    assert (Hr : length D = S n + length (skipn (S n) D)).
    { rewrite length_skipn; lia. }
    pose proof (nth_error_subst_prefix u D n X HD) as HL.
    rewrite subst_var_lt_typing by lia.
    rewrite Hr, subst_lift_offset by lia.
    apply check_of_synth. eapply sy_var; [exact Hwf|].
    rewrite nth_error_app1; [exact HL|].
    rewrite subst_prefix_length; lia.
  - subst n.
    assert (HX : X = A0).
    { rewrite nth_error_app2 in Hnth by lia.
      replace (length D - length D) with 0 in Hnth by lia.
      cbn in Hnth. inversion Hnth. reflexivity. }
    subst X. rewrite subst_var_eq_typing.
    pose proof (check_lift_into (subst_prefix u D) G u A0 Hu Hwf) as HC.
    rewrite subst_prefix_length in HC.
    rewrite subst_lift_delete by lia. exact HC.
  - rewrite subst_var_gt_typing by lia.
    rewrite subst_lift_delete by lia.
    replace (lift n 0 X) with (lift (S (pred n)) 0 X) by (f_equal; lia).
    apply check_of_synth. eapply sy_var; [exact Hwf|].
    rewrite nth_error_app2 by (rewrite subst_prefix_length; lia).
    rewrite subst_prefix_length.
    rewrite nth_error_app2 in Hnth by lia.
    replace (pred n - length D) with (pred (n - length D)) by lia.
    remember (n - length D) as q eqn:Hq.
    destruct q as [|q]; [lia|]. cbn in Hnth |- *. exact Hnth.
Qed.


Lemma subst_Sig_typing : forall IT E u k,
    subst u k (Sig IT E) = Sig (subst u k IT) (subst u k E).
Proof.
  intros. unfold Sig, Label. cbn [subst].
  rewrite !subst_lift_one_zero. reflexivity.
Qed.

Lemma subst_Carrier_typing : forall E Sf u k,
    subst u k (Carrier E Sf) = Carrier (subst u k E) (subst u k Sf).
Proof.
  intros. unfold Carrier, Full, branches. cbn [subst].
  repeat rewrite subst_lift_one_zero. reflexivity.
Qed.

Theorem typing_subst_mutual :
  (forall Gamma (H : wf Gamma), wf_subst_property Gamma H) /\
  (forall Gamma t T (H : synth Gamma t T), synth_subst_property Gamma t T H) /\
  (forall Gamma t T (H : check Gamma t T), check_subst_property Gamma t T H) /\
  (forall Gamma Sf i E Q bs (H : check_branches Gamma Sf i E Q bs),
      branches_subst_property Gamma Sf i E Q bs H) /\
  (forall Gamma S T (H : sub Gamma S T), sub_subst_property Gamma S T H).
Proof.
 apply typing_subst_ind; unfold wf_subst_property,
    synth_subst_property, check_subst_property,
    branches_subst_property, sub_subst_property,
    subst_ctx, subst_branches; intros; subst.
 - destruct D; discriminate.
 - destruct D as [|X D']; cbn in H1 |- *.
   + inversion H1; subst. inversion w; subst; assumption.
   + inversion H1; subst X. eapply wf_cons with (k:=k).
     * eapply H; [exact H5|exact H2].
     * eapply H0; [exact H5|exact H2].
 - pose proof (H D A0 G0 u eq_refl H1) as Hwf.
   destruct (Nat.lt_trichotomy n (length D)) as [Hlt|[Heq|Hgt]].
   + assert (HD : nth_error D n = Some A).
     { rewrite nth_error_app1 in e; auto. }
     assert (Hr : length D = S n + length (skipn (S n) D)).
     { rewrite length_skipn. lia. }
     assert (HL := nth_error_subst_prefix u D n A HD).
     rewrite subst_var_lt_typing by lia.
     rewrite Hr, subst_lift_offset by lia.
     apply check_of_synth. eapply sy_var; [exact Hwf|].
     rewrite nth_error_app1; [exact HL|]. rewrite subst_prefix_length; lia.
   + subst n.
     assert (HA : A = A0).
     { rewrite nth_error_app2 in e by lia.
       replace (length D - length D) with 0 in e by lia.
       cbn in e. inversion e. reflexivity. }
     subst A.
     rewrite subst_var_eq_typing.
     pose proof (check_lift_into (subst_prefix u D) G0 u A0 H1 Hwf) as HC.
     rewrite subst_prefix_length in HC.
     rewrite subst_lift_delete by lia. exact HC.
   + rewrite subst_var_gt_typing by lia.
     rewrite subst_lift_delete by lia.
     replace (lift n 0 A) with (lift (S (pred n)) 0 A) by (f_equal; lia).
     apply check_of_synth. eapply sy_var; [exact Hwf|].
     rewrite nth_error_app2 by (rewrite subst_prefix_length; lia).
     rewrite subst_prefix_length.
     rewrite nth_error_app2 in e by lia. cbn in e.
     replace (Nat.pred n - length D) with (Nat.pred (n-length D)) by lia.
     remember (n - length D) as q eqn:Hq.
     destruct q as [|q]; [lia|]. cbn in e |- *. exact e.
 - apply check_of_synth. cbn. apply sy_sort. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_pi.
   + eapply H; [reflexivity|exact H2].
   + eapply H0 with (D := A :: D); [reflexivity|exact H2].
 - apply check_of_synth. cbn. apply sy_sigma.
   + eapply H; [reflexivity|exact H2].
   + eapply H0 with (D := A :: D); [reflexivity|exact H2].
 - rewrite subst_subst_zero_comm. cbn. eapply ch_app.
   + eapply H; [reflexivity|exact H3].
   + eapply ch_expand.
     * apply cv_sym, conv_of_eval. exact (eval_subst_typing _ _ e u (length D)).
     * eapply H0; [reflexivity|exact H3].
   + eapply H1; [reflexivity|exact H3].
 - cbn. eapply ch_fst.
   + eapply H; [reflexivity|exact H2].
   + eapply ch_expand.
     * apply cv_sym, conv_of_eval. exact (eval_subst_typing _ _ e u (length D)).
     * eapply H0; [reflexivity|exact H2].
 - rewrite subst_subst_zero_comm. cbn. eapply ch_snd.
   + eapply H; [reflexivity|exact H2].
   + eapply ch_expand.
     * apply cv_sym, conv_of_eval. exact (eval_subst_typing _ _ e u (length D)).
     * eapply H0; [reflexivity|exact H2].
 - apply check_of_synth. cbn. apply sy_unitT. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_unit. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_uid. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_enumu. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_tag. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_nile. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_conse.
   + eapply H; [reflexivity|exact H2].
   + eapply H0; [reflexivity|exact H2].
 - apply check_of_synth. cbn. apply sy_enumt. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_epi.
   + eapply H; [reflexivity|exact H2].
   + eapply H0; [reflexivity|exact H2].
 - apply check_of_synth. cbn. apply sy_switch with (k:=k).
   + eapply H; [reflexivity|exact H4].
   + eapply H0; [reflexivity|exact H4].
   + eapply H1; [reflexivity|exact H4].
   + eapply H2; [reflexivity|exact H4].
 - apply check_of_synth. cbn. apply sy_idesc. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_interp with (IT:=subst u (length D0) IT).
   + eapply H; [reflexivity|exact H3].
   + eapply H0; [reflexivity|exact H3].
   + eapply H1; [reflexivity|exact H3].
 - apply check_of_synth. cbn. apply sy_mui with (IT:=subst u (length D) IT).
   + eapply H; [reflexivity|exact H2].
   + specialize (H0 D A G0 u eq_refl H2). cbn in H0.
     rewrite subst_lift_one_zero in H0. exact H0.
 - apply check_of_synth. cbn. apply sy_iall with (IT:=subst u (length D0) IT).
   + eapply H; [reflexivity|exact H5].
   + eapply H0; [reflexivity|exact H5].
   + eapply H1; [reflexivity|exact H5].
   + eapply H2; [reflexivity|exact H5].
   + specialize (H3 D0 A G0 u eq_refl H5). cbn in H3.
     rewrite subst_lift_one_zero in H3. exact H3.
 - apply check_of_synth. cbn. apply sy_hyps with (IT:=subst u (length D0) IT).
   + eapply H; [reflexivity|exact H6].
   + eapply H0; [reflexivity|exact H6].
   + eapply H1; [reflexivity|exact H6].
   + specialize (H2 D0 A G0 u eq_refl H6). cbn in H2.
     rewrite subst_lift_one_zero in H2. exact H2.
   + specialize (H3 D0 A G0 u eq_refl H6). cbn in H3.
     rewrite subst_lift_one_zero, subst_lift_two_zero in H3. exact H3.
   + eapply H4; [reflexivity|exact H6].
 - apply check_of_synth. cbn. apply sy_ind with (IT:=subst u (length D) IT).
   + eapply H; [reflexivity|exact H6].
   + specialize (H0 D A G0 u eq_refl H6). cbn in H0.
     rewrite subst_lift_one_zero in H0. exact H0.
   + specialize (H1 D A G0 u eq_refl H6). cbn in H1.
     rewrite subst_lift_one_zero in H1. exact H1.
   + specialize (H2 D A G0 u eq_refl H6). cbn in H2.
     repeat rewrite subst_lift_one_zero in H2.
     repeat rewrite subst_lift_two_zero in H2.
     replace (S(S(S(length D)))) with (3+length D) in H2 by lia.
     rewrite (subst_lift_offset P u 3 0 (length D)) in H2 by lia.
     exact H2.
   + eapply H3; [reflexivity|exact H6].
   + eapply H4; [reflexivity|exact H6].
 - apply check_of_synth. cbn. apply sy_mus with
     (IT:=subst u (length D) IT) (E:=subst u (length D) E).
   + eapply H; [reflexivity|exact H3].
   + eapply H0; [reflexivity|exact H3].
   + specialize (H1 D A G0 u eq_refl H3).
     assert (Ety :
       subst u (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
       TPi (subst u (length D) IT)
         (Sig (lift 1 0 (subst u (length D) IT))
              (lift 1 0 (subst u (length D) E)))).
     { change
         (TPi (subst u (length D) IT)
            (subst u (S (length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
          TPi (subst u (length D) IT)
            (Sig (lift 1 0 (subst u (length D) IT))
                 (lift 1 0 (subst u (length D) E)))).
       rewrite subst_Sig_typing, !subst_lift_one_zero. reflexivity. }
     rewrite <- Ety. exact H1.
 - apply check_of_synth. cbn. eapply sy_case with
     (Sf:=subst u (length D) Sf) (i:=subst u (length D) i)
     (IT:=subst u (length D) IT) (E:=subst u (length D) E)
     (k:=k) (Phi:=subst u (length D) Phi).
   + eapply H; [reflexivity|exact H7].
   + eapply H0; [reflexivity|exact H7].
   + eapply H1; [reflexivity|exact H7].
   + specialize (H2 D A G0 u eq_refl H7).
     assert (Ety : subst u (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
       TPi (subst u (length D) IT)
         (Sig (lift 1 0 (subst u (length D) IT))
              (lift 1 0 (subst u (length D) E)))).
     { change (TPi (subst u (length D) IT)
          (subst u (S(length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (subst u (length D) IT)
          (Sig (lift 1 0 (subst u (length D) IT))
               (lift 1 0 (subst u (length D) E)))).
       rewrite subst_Sig_typing, !subst_lift_one_zero. reflexivity. }
     rewrite <- Ety. exact H2.
   + eapply H3; [reflexivity|exact H7].
   + eapply H4; [reflexivity|exact H7].
   + change (distinct (map fst (subst_branches u (length D) bs))).
     rewrite map_fst_subst_branches. exact (distinct_subst _ d u (length D)).
   + exact (eval_subst_typing _ _ e u (length D)).
   + change (covers (map fst (subst_branches u (length D) bs))
                    (subst u (length D) Phi)).
     rewrite map_fst_subst_branches. exact (covers_subst _ _ c5 u (length D)).
   + eapply H5; [reflexivity|exact H7].
 - apply check_of_synth. cbn. apply sy_list. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_lnil. eapply H; [reflexivity|exact H1].
 - apply check_of_synth. cbn. apply sy_lcons.
   + eapply H; [reflexivity|exact H3].
   + eapply H0; [reflexivity|exact H3].
   + eapply H1; [reflexivity|exact H3].
 - eapply ch_expand.
   + apply cv_sym. exact (conv_subst_same _ _ c u (length D)).
   + eapply H; [reflexivity|exact H1].
 - eapply ch_sub.
   + eapply H; [reflexivity|exact H2].
   + eapply H0; [reflexivity|exact H2].
 - eapply ch_expand.
   + exact (conv_subst_same _ _ c u (length D)).
   + eapply H; [reflexivity|exact H1].
 - cbn. apply ch_lam. eapply H with (D:=A::D); [reflexivity|exact H1].
 - cbn. apply ch_pair.
   + eapply H; [reflexivity|exact H2].
   + specialize (H0 D A0 G0 u eq_refl H2).
     rewrite subst_subst_zero_comm in H0. exact H0.
 - cbn. rewrite subst_subst_zero_comm. eapply ch_app.
   + eapply H; [reflexivity|exact H3].
   + eapply H0; [reflexivity|exact H3].
   + eapply H1; [reflexivity|exact H3].
 - cbn. eapply ch_fst.
   + eapply H; [reflexivity|exact H2].
   + eapply H0; [reflexivity|exact H2].
 - cbn. rewrite subst_subst_zero_comm. eapply ch_snd.
   + eapply H; [reflexivity|exact H2].
   + eapply H0; [reflexivity|exact H2].
 - cbn. apply ch_ezero.
   + eapply H; [reflexivity|exact H2].
   + eapply H0; [reflexivity|exact H2].
 - cbn. apply ch_esucc.
   + eapply H; [reflexivity|exact H2].
   + eapply H0; [reflexivity|exact H2].
 - cbn. apply ch_ivar. eapply H; [reflexivity|exact H1].
 - cbn. apply ch_i1. eapply H; [reflexivity|exact H1].
 - cbn. apply ch_iprod.
   + eapply H; [reflexivity|exact H2].
   + eapply H0; [reflexivity|exact H2].
 - cbn. apply ch_ipi.
   + eapply H; [reflexivity|exact H2].
   + specialize (H0 D A G0 u eq_refl H2). cbn in H0.
     rewrite subst_lift_one_zero in H0. exact H0.
 - cbn. apply ch_isig.
   + eapply H; [reflexivity|exact H2].
   + specialize (H0 D A G0 u eq_refl H2). cbn in H0.
     rewrite subst_lift_one_zero in H0. exact H0.
 - cbn. apply ch_ichoice.
   + eapply H; [reflexivity|exact H2].
   + specialize (H0 D A G0 u eq_refl H2). cbn in H0.
     rewrite subst_lift_one_zero in H0. exact H0.
 - cbn. apply ch_in_mui with (IT:=subst u (length D) IT).
   + eapply H; [reflexivity|exact H4].
   + specialize (H0 D A G0 u eq_refl H4). cbn in H0.
     rewrite subst_lift_one_zero in H0. exact H0.
   + eapply H1; [reflexivity|exact H4].
   + eapply H2; [reflexivity|exact H4].
 - cbn. eapply ch_in_sig with
     (IT:=subst u (length D) IT) (E:=subst u (length D) E)
     (Phi:=subst u (length D) Phi).
   + eapply H; [reflexivity|exact H6].
   + eapply H0; [reflexivity|exact H6].
   + specialize (H1 D A G0 u eq_refl H6).
     assert (Ety : subst u (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
       TPi (subst u (length D) IT)
         (Sig (lift 1 0 (subst u (length D) IT))
              (lift 1 0 (subst u (length D) E)))).
     { change (TPi (subst u (length D) IT)
          (subst u (S(length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (subst u (length D) IT)
          (Sig (lift 1 0 (subst u (length D) IT))
               (lift 1 0 (subst u (length D) E)))).
       rewrite subst_Sig_typing, !subst_lift_one_zero. reflexivity. }
     rewrite <- Ety. exact H1.
   + eapply H2; [reflexivity|exact H6].
   + eapply H3; [reflexivity|exact H6].
   + exact (eval_subst_typing _ _ e u (length D)).
   + exact (spine_mem_subst _ _ s u (length D)).
   + specialize (H4 D A G0 u eq_refl H6).
     rewrite <- subst_Carrier_typing.
     exact H4.
 - cbn. constructor.
 - cbn. apply cb_cons.
   + eapply H; [reflexivity|exact H3].
   + specialize (H0
       (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)::D)
       A G0 u eq_refl H3).
     cbn in H0. repeat rewrite subst_lift_one_zero in H0.
     exact H0.
   + eapply H1; [reflexivity|exact H3].
 - apply su_conv. exact (conv_subst_same _ _ c u (length D)).
 - eapply su_trans.
   + eapply H; [reflexivity|exact H2].
   + eapply H0; [reflexivity|exact H2].
 - cbn. apply su_sort. exact l.
 - cbn. apply su_pi.
   + eapply H; [reflexivity|exact H2].
   + eapply H0 with (D:=A'::D); [reflexivity|exact H2].
 - change (sub (subst_prefix u D++G0)
     (TApp (SigMu (subst u (length D) E) (subst u (length D) Sf))
       (subst u (length D) i))
     (TApp (subst u (length D) (Carrier E Sf)) (subst u (length D) i))).
   rewrite subst_Carrier_typing. eapply su_forget with
     (IT:=subst u (length D) IT) (E:=subst u (length D) E).
   + eapply H; [reflexivity|exact H4].
   + eapply H0; [reflexivity|exact H4].
   + specialize (H1 D A G0 u eq_refl H4).
     assert (Ety : subst u (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
       TPi (subst u (length D) IT)
         (Sig (lift 1 0 (subst u (length D) IT))
              (lift 1 0 (subst u (length D) E)))).
     { change (TPi (subst u (length D) IT)
          (subst u (S(length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (subst u (length D) IT)
          (Sig (lift 1 0 (subst u (length D) IT))
               (lift 1 0 (subst u (length D) E)))).
       rewrite subst_Sig_typing, !subst_lift_one_zero. reflexivity. }
     rewrite <- Ety. exact H1.
   + eapply H2; [reflexivity|exact H4].
 - cbn. eapply su_sig with
     (IT:=subst u (length D) IT) (E:=subst u (length D) E)
     (Phi1:=subst u (length D) Phi1) (Phi2:=subst u (length D) Phi2).
   + eapply H; [reflexivity|exact H5].
   + eapply H0; [reflexivity|exact H5].
   + specialize (H1 D A G0 u eq_refl H5).
     assert (Ety1 : subst u (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
       TPi (subst u (length D) IT)
         (Sig (lift 1 0 (subst u (length D) IT))
              (lift 1 0 (subst u (length D) E)))).
     { change (TPi (subst u (length D) IT)
          (subst u (S(length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (subst u (length D) IT)
          (Sig (lift 1 0 (subst u (length D) IT))
               (lift 1 0 (subst u (length D) E)))).
       rewrite subst_Sig_typing, !subst_lift_one_zero. reflexivity. }
     rewrite <- Ety1. exact H1.
   + specialize (H2 D A G0 u eq_refl H5).
     assert (Ety2 : subst u (length D) (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) =
       TPi (subst u (length D) IT)
         (Sig (lift 1 0 (subst u (length D) IT))
              (lift 1 0 (subst u (length D) E)))).
     { change (TPi (subst u (length D) IT)
          (subst u (S(length D)) (Sig (lift 1 0 IT) (lift 1 0 E))) =
        TPi (subst u (length D) IT)
          (Sig (lift 1 0 (subst u (length D) IT))
               (lift 1 0 (subst u (length D) E)))).
       rewrite subst_Sig_typing, !subst_lift_one_zero. reflexivity. }
     rewrite <- Ety2. exact H2.
   + specialize (conv_subst_same _ _ c3 u (length D)) as HC.
     cbn in HC. repeat rewrite subst_lift_one_zero in HC. exact HC.
   + exact (eval_subst_typing _ _ e u (length D)).
   + exact (eval_subst_typing _ _ e0 u (length D)).
   + exact (spine_incl_subst _ _ s u (length D)).
   + eapply H3; [reflexivity|exact H5].
Qed.

Theorem check_subst : forall D G A u t T,
    check (D ++ A :: G) t T -> check G u A ->
    check (subst_ctx u D G)
      (subst u (length D) t) (subst u (length D) T).
Proof.
  intros D G A u t T Hck Hu.
  destruct typing_subst_mutual as [_ [_ [HC _]]].
  eapply (HC _ _ _ Hck D A G u); [reflexivity | exact Hu].
Qed.

Theorem check_subst0 : forall G A u t T,
    check (A :: G) t T -> check G u A ->
    check G (subst u 0 t) (subst u 0 T).
Proof.
  intros G A u t T Hck Hu.
  exact (check_subst [] G A u t T Hck Hu).
Qed.

Theorem sub_subst : forall D G A u S T,
    sub (D ++ A :: G) S T -> check G u A ->
    sub (subst_ctx u D G)
      (subst u (length D) S) (subst u (length D) T).
Proof.
  intros D G A u S T Hsub Hu.
  destruct typing_subst_mutual as [_ [_ [_ [_ HS]]]].
  eapply (HS _ _ _ Hsub D A G u); [reflexivity | exact Hu].
Qed.

Theorem sub_subst0 : forall G A u S T,
    sub (A :: G) S T -> check G u A ->
    sub G (subst u 0 S) (subst u 0 T).
Proof.
  intros G A u S T Hsub Hu.
  exact (sub_subst [] G A u S T Hsub Hu).
Qed.

Print Assumptions spine_mem_subst.
Print Assumptions spine_incl_subst.
Print Assumptions covers_subst.
Print Assumptions distinct_subst.
Print Assumptions spine_incl_lift.
Print Assumptions covers_lift.
Print Assumptions distinct_lift.
