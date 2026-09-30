Require Import Progress _tmp_eta_shape _luna_enum_pos_lift_inv.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Ltac take_term_lift_inv :=
  match goal with
  | IH : forall (x : term) (q : nat),
      lift 1 ?q0 ?x0 = lift 1 q x ->
      exists y, ?target = lift 1 q y /\ pstep x y |- _ =>
      let y := fresh "y" in
      let Ey := fresh "Ey" in
      let Hy := fresh "Hy" in
      destruct (IH x0 q0 eq_refl) as [y [Ey Hy]];
      subst target; clear IH
  end.

Ltac take_branch_lift_inv :=
  match goal with
  | IH : forall (src : list (term * term)) (q : nat),
      map (fun '(c,b) => (lift 1 ?q0 c, lift 1 (S ?q0) b)) ?src0 =
        map (fun '(c,b) => (lift 1 q c, lift 1 (S q) b)) src ->
      exists dst,
        ?target = map (fun '(c,b) => (lift 1 q c, lift 1 (S q) b)) dst /\
        pbranches src dst |- _ =>
      let dst := fresh "dst" in
      let Edst := fresh "Edst" in
      let Hdst := fresh "Hdst" in
      destruct (IH src0 q0 eq_refl) as [dst [Edst Hdst]];
      subst target; clear IH
  end.

Ltac apply_core_root :=
  first
    [ eapply ps_beta; eassumption
    | eapply ps_fst_pair; eassumption
    | eapply ps_snd_pair; eassumption
    | eapply ps_epi_nil; eassumption
    | eapply ps_epi_cons; eassumption
    | eapply ps_switch_zero; eassumption
    | eapply ps_switch_succ; eassumption
    | eapply ps_interp_var; eassumption
    | eapply ps_interp_one; eassumption
    | eapply ps_interp_prod; eassumption
    | eapply ps_interp_pi; eassumption
    | eapply ps_interp_sig; eassumption
    | eapply ps_interp_choice; eassumption
    | eapply ps_iall_var; eassumption
    | eapply ps_iall_one; eassumption
    | eapply ps_iall_prod; eassumption
    | eapply ps_iall_pi; eassumption
    | eapply ps_iall_sig; eassumption
    | eapply ps_iall_choice; eassumption
    | eapply ps_hyps_var; eassumption
    | eapply ps_hyps_one; eassumption
    | eapply ps_hyps_prod; eassumption
    | eapply ps_hyps_pi; eassumption
    | eapply ps_hyps_sig; eassumption
    | eapply ps_hyps_choice; eassumption
    | eapply ps_ind_red; eassumption ].

Lemma pstep_lift_inv_mut :
  (forall t u (H : pstep t u), forall f k,
      t = lift 1 k f ->
      exists v, u = lift 1 k v /\ pstep f v) /\
  (forall bs bs' (H : pbranches bs bs'), forall src k,
      bs = map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) src ->
      exists dst,
        bs' = map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) dst /\
        pbranches src dst).
Proof.
  apply pstep_pbranches_ind; intros.
  all: repeat match goal with
  | E : ?source = lift 1 ?q ?x |- _ =>
      destruct x; cbn [lift] in E;
      repeat match type of E with
      | context [Nat.ltb ?a ?b] => destruct (Nat.ltb a b) eqn:?
      end;
      try discriminate;
      inversion E; subst; clear E
  end.
  all: repeat match goal with
  | E : ?source = map
      (fun '(c,b) => (lift 1 ?q c, lift 1 (S ?q) b)) ?xs |- _ =>
      destruct xs as [|[xc xb] xs]; cbn in E; try discriminate;
      inversion E; subst; clear E
  end.
  all: repeat take_term_lift_inv.
  all: repeat take_branch_lift_inv.
  all: try solve [
    eexists; split; cycle 1;
    [ constructor; eassumption
    | cbn [lift]; repeat match goal with
      | Hlt : Nat.ltb _ _ = _ |- _ => rewrite Hlt
      end; reflexivity ]].
  all: try solve [
    eexists; split; cycle 1;
    [ apply_core_root
    | cbn [lift];
      repeat rewrite lift_subst_zero_comm;
      repeat rewrite (lift_lift_one_zero _ _ _);
      repeat rewrite (lift_lift_one_one _ _ _);
      repeat rewrite (lift_lift_two_zero _ _ _);
      reflexivity ]].
  rewrite nth_error_map in e.
  destruct (nth_error bs0 k) as [[c0 b0]|] eqn:Hnth;
    cbn in e; try discriminate.
  inversion e; subst c b; clear e.
  destruct (H0 b0 (S k0) eq_refl) as [bd [Hbd Hpbd]].
  subst b'.
  exists (subst y 0 bd). split.
  - rewrite lift_subst_zero_comm. reflexivity.
  - eapply ps_case_red with (k := k) (c := c0) (b := b0) (n := n).
    + exact Hnth.
    + eapply enum_pos_lift_inv_luna. exact e0.
    + eapply enum_pos_lift_inv_luna. exact e1.
    + intros j cj bj Hj Horig.
      assert (Hmapped :
          nth_error
            (map (fun '(c,b) => (lift 1 k0 c, lift 1 (S k0) b)) bs0) j =
          Some (lift 1 k0 cj, lift 1 (S k0) bj)).
      { rewrite nth_error_map, Horig. reflexivity. }
      destruct (e2 j (lift 1 k0 cj) (lift 1 (S k0) bj) Hj Hmapped)
        as [nj [Hpos Hneq]].
      exists nj. split; [eapply enum_pos_lift_inv_luna |]; eassumption.
    + exact Hy.
    + exact Hpbd.
Qed.

Corollary pstep_lift_inv : forall f k T,
    pstep (lift 1 k f) T ->
    exists u, T = lift 1 k u /\ pstep f u.
Proof.
  intros f k T H.
  exact (proj1 pstep_lift_inv_mut _ _ H f k eq_refl).
Qed.

Corollary pbranches_lift_inv : forall bs k BS,
    pbranches
      (map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) bs) BS ->
    exists us,
      BS = map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) us /\
      pbranches bs us.
Proof.
  intros bs k BS H.
  exact (proj2 pstep_lift_inv_mut _ _ H bs k eq_refl).
Qed.
