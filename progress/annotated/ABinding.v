(* Binding algebra for annotated terms. Adapted from the checked raw
   algebra in nameless/DBParallelBase.v; induction now also covers every
   annotation and its own binder depth. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export annotated.ASyntax.

Lemma subst_lift_var : forall v c u,
    subst u c (lift 1 c (TVar v)) = TVar v.
Proof.
  intros v c u. cbn [lift].
  destruct (Nat.ltb v c) eqn:Hnk.
  - cbn [subst Nat.pred]. rewrite Hnk. reflexivity.
  - apply Nat.ltb_ge in Hnk. cbn [subst Nat.pred].
    destruct (Nat.ltb (1 + v) c) eqn:Hlift.
    + apply Nat.ltb_lt in Hlift. lia.
    + destruct (Nat.eqb (1 + v) c) eqn:Heq.
      * exfalso. pose proof (proj1 (Nat.eqb_eq (1 + v) c) Heq). lia.
      * f_equal.
Qed.

Lemma subst_lift_cancel : forall t u c, subst u c (lift 1 c t) = t.
Proof.
  induction t; intros u c; cbn [lift subst];
    try solve [apply subst_lift_var]; try reflexivity;
    f_equal; auto.
Qed.

Lemma subst_lift_zero : forall f w, subst w 0 (lift 1 0 f) = f.
Proof. intros; apply subst_lift_cancel. Qed.

Lemma lift_zero_id : forall t c, lift 0 c t = t.
Proof.
  induction t; intros c;
    try solve [cbn [lift]; destruct (Nat.ltb n c); reflexivity];
    cbn; try reflexivity;
    f_equal; auto.
Qed.

Lemma lift_lift_comm_var : forall v d m c1 c2, c1 <= c2 ->
    lift d (m+c2) (lift m c1 (TVar v)) = lift m c1 (lift d c2 (TVar v)).
Proof.
  intros v d m c1 c2 Hij. cbn [lift].
  destruct (Nat.ltb v c1) eqn:Hni; destruct (Nat.ltb v c2) eqn:Hnj; cbn [lift].
  - apply Nat.ltb_lt in Hni. apply Nat.ltb_lt in Hnj.
    assert (Hout : Nat.ltb v (m+c2) = true) by (apply Nat.ltb_lt; lia).
    rewrite Hout. rewrite <- Nat.ltb_lt in Hni. rewrite Hni. reflexivity.
  - apply Nat.ltb_lt in Hni. apply Nat.ltb_ge in Hnj. lia.
  - apply Nat.ltb_ge in Hni. apply Nat.ltb_lt in Hnj.
    assert (Hout : Nat.ltb (m+v) (m+c2) = true) by (apply Nat.ltb_lt; lia).
    rewrite Hout. rewrite <- Nat.ltb_ge in Hni. rewrite Hni. reflexivity.
  - apply Nat.ltb_ge in Hni. apply Nat.ltb_ge in Hnj.
    assert (Hout : Nat.ltb (m+v) (m+c2) = false) by (apply Nat.ltb_ge; lia).
    assert (Hin : Nat.ltb (d+v) c1 = false) by (apply Nat.ltb_ge; lia).
    rewrite Hout, Hin. f_equal. lia.
Qed.

Lemma lift_lift_comm : forall t d m c1 c2, c1 <= c2 ->
    lift d (m + c2) (lift m c1 t) = lift m c1 (lift d c2 t).
Proof.
  induction t; intros d m c1 c2 Hij;
    try solve [apply lift_lift_comm_var; exact Hij];
    cbn; try (replace (S (m + c2)) with (m + S c2) by lia);
    try reflexivity; f_equal; auto using le_n_S.
Qed.

Corollary lift_lift_zero_comm : forall t d m c,
    lift d (m+c) (lift m 0 t) = lift m 0 (lift d c t).
Proof. intros; apply lift_lift_comm; lia. Qed.

Corollary lift_lift_one_zero : forall t d c,
    lift d (S c) (lift 1 0 t) = lift 1 0 (lift d c t).
Proof.
  intros t d c. replace (S c) with (1+c) by lia. apply lift_lift_comm; lia.
Qed.

Corollary lift_lift_one_one : forall t d c,
    lift d (S (S c)) (lift 1 1 t) = lift 1 1 (lift d (S c) t).
Proof.
  intros t d c. replace (S (S c)) with (1+S c) by lia.
  apply lift_lift_comm; lia.
Qed.

Corollary lift_lift_two_zero : forall t d c,
    lift d (S (S c)) (lift 2 0 t) = lift 2 0 (lift d c t).
Proof.
  intros t d c. replace (S (S c)) with (2+c) by lia.
  apply lift_lift_comm; lia.
Qed.

Lemma lift_fuse_var : forall v d m y c1, c1 <= m ->
    lift d (y+c1) (lift m y (TVar v)) = lift (d+m) y (TVar v).
Proof.
  intros v d m y c1 Hie. cbn [lift].
  destruct (Nat.ltb v y) eqn:Hnq; cbn [lift].
  - apply Nat.ltb_lt in Hnq.
    assert (Hout : Nat.ltb v (y+c1) = true) by (apply Nat.ltb_lt; lia).
    rewrite Hout. reflexivity.
  - apply Nat.ltb_ge in Hnq.
    assert (Hout : Nat.ltb (m+v) (y+c1) = false) by (apply Nat.ltb_ge; lia).
    rewrite Hout. f_equal. lia.
Qed.

Lemma lift_fuse : forall t d m y c1, c1 <= m ->
    lift d (y+c1) (lift m y t) = lift (d+m) y t.
Proof.
  induction t; intros d m y c1 Hie;
    try solve [apply lift_fuse_var; exact Hie];
    cbn; try (replace (S (y + c1)) with (S y + c1) by lia);
    try reflexivity; f_equal; auto.
Qed.

Corollary lift_fuse_zero : forall t d m c1, c1 <= m ->
    lift d c1 (lift m 0 t) = lift (d+m) 0 t.
Proof.
  intros t d m c1 H. replace c1 with (0+c1) by lia. apply lift_fuse. exact H.
Qed.

Lemma subst_lift_offset_var : forall v u m c1 c2, c1 <= c2 ->
    subst u (m+c2) (lift m c1 (TVar v)) = lift m c1 (subst u c2 (TVar v)).
Proof.
  intros v u m c1 c2 Hij.
  destruct (Nat.lt_trichotomy v c1) as [Hni | [Hni | Hni]].
  - assert (Hli : Nat.ltb v c1 = true) by (apply Nat.ltb_lt; lia).
    assert (Hlj : Nat.ltb v c2 = true) by (apply Nat.ltb_lt; lia).
    assert (Hlo : Nat.ltb v (m+c2) = true) by (apply Nat.ltb_lt; lia).
    cbn [lift subst Nat.pred]. rewrite Hli, Hlj. cbn [subst lift Nat.pred].
    rewrite Hlo, Hli. reflexivity.
  - subst v.
    destruct (Nat.eq_dec c1 c2) as [-> | Hij'].
    + assert (Hli : Nat.ltb c2 c2 = false) by (apply Nat.ltb_ge; lia).
      assert (Hei : Nat.eqb c2 c2 = true) by (apply Nat.eqb_eq; reflexivity).
      assert (Hlo : Nat.ltb (m+c2) (m+c2) = false) by (apply Nat.ltb_ge; lia).
      assert (Heo : Nat.eqb (m+c2) (m+c2) = true) by (apply Nat.eqb_eq; reflexivity).
      cbn [lift subst Nat.pred]. rewrite Hli, Hei. cbn [subst Nat.pred]. rewrite Hlo, Heo.
      symmetry. apply lift_fuse_zero. lia.
    + assert (Hli : Nat.ltb c1 c1 = false) by (apply Nat.ltb_ge; lia).
      assert (Hlj : Nat.ltb c1 c2 = true) by (apply Nat.ltb_lt; lia).
      assert (Hlo : Nat.ltb (m+c1) (m+c2) = true) by (apply Nat.ltb_lt; lia).
      cbn [lift subst Nat.pred]. rewrite Hli, Hlj. cbn [subst lift Nat.pred].
      rewrite Hlo, Hli. reflexivity.
  - destruct (Nat.lt_trichotomy v c2) as [Hnj | [Hnj | Hnj]].
    + assert (Hli : Nat.ltb v c1 = false) by (apply Nat.ltb_ge; lia).
      assert (Hlj : Nat.ltb v c2 = true) by (apply Nat.ltb_lt; lia).
      assert (Hlo : Nat.ltb (m+v) (m+c2) = true) by (apply Nat.ltb_lt; lia).
      cbn [lift subst Nat.pred]. rewrite Hli, Hlj. cbn [subst lift Nat.pred].
      rewrite Hlo, Hli. reflexivity.
    + subst v.
      assert (Hli : Nat.ltb c2 c1 = false) by (apply Nat.ltb_ge; lia).
      assert (Hlj : Nat.ltb c2 c2 = false) by (apply Nat.ltb_ge; lia).
      assert (Hej : Nat.eqb c2 c2 = true) by (apply Nat.eqb_eq; reflexivity).
      assert (Hlo : Nat.ltb (m+c2) (m+c2) = false) by (apply Nat.ltb_ge; lia).
      assert (Heo : Nat.eqb (m+c2) (m+c2) = true) by (apply Nat.eqb_eq; reflexivity).
      cbn [lift subst Nat.pred]. rewrite Hli, Hlj, Hej. cbn [subst Nat.pred]. rewrite Hlo, Heo.
      symmetry. apply lift_fuse_zero. lia.
    + assert (Hli : Nat.ltb v c1 = false) by (apply Nat.ltb_ge; lia).
      assert (Hlj : Nat.ltb v c2 = false) by (apply Nat.ltb_ge; lia).
      assert (Hej : Nat.eqb v c2 = false) by (apply Nat.eqb_neq; lia).
      assert (Hlo : Nat.ltb (m+v) (m+c2) = false) by (apply Nat.ltb_ge; lia).
      assert (Heo : Nat.eqb (m+v) (m+c2) = false) by (apply Nat.eqb_neq; lia).
      assert (Hpred : Nat.ltb (Nat.pred v) c1 = false)
        by (apply Nat.ltb_ge; destruct v; cbn in *; lia).
      cbn [lift subst Nat.pred]. rewrite Hli, Hlj, Hej. cbn [subst lift Nat.pred].
      rewrite Hlo, Heo, Hpred. f_equal. destruct v; cbn in *; lia.
Qed.

Lemma subst_lift_offset : forall t u m c1 c2, c1 <= c2 ->
    subst u (m+c2) (lift m c1 t) = lift m c1 (subst u c2 t).
Proof.
  induction t; intros u m c1 c2 Hij;
    try solve [apply subst_lift_offset_var; exact Hij];
    cbn; try (replace (S (m + c2)) with (m + S c2) by lia);
    try reflexivity; f_equal; auto using le_n_S.
Qed.

Corollary subst_lift_one_zero : forall t u c,
    subst u (S c) (lift 1 0 t) = lift 1 0 (subst u c t).
Proof.
  intros t u c. replace (S c) with (1+c) by lia. apply subst_lift_offset. lia.
Qed.

Corollary subst_lift_one_one : forall t u c,
    subst u (S (S c)) (lift 1 1 t) = lift 1 1 (subst u (S c) t).
Proof.
  intros t u c. replace (S (S c)) with (1+S c) by lia.
  apply subst_lift_offset. lia.
Qed.

Corollary subst_lift_two_zero : forall t u c,
    subst u (S (S c)) (lift 2 0 t) = lift 2 0 (subst u c t).
Proof.
  intros t u c. replace (S (S c)) with (2+c) by lia.
  apply subst_lift_offset. lia.
Qed.

Lemma subst_subst_comm_var : forall v u w c c2,
    subst u (c2+c) (subst w c2 (TVar v)) =
    subst (subst u c w) c2 (subst u (c2+S c) (TVar v)).
Proof.
  intros v u w c c2.
  destruct (Nat.lt_trichotomy v c2) as [Hnj | [Hnj | Hnj]].
  - assert (H1 : Nat.ltb v c2 = true) by (apply Nat.ltb_lt; lia).
    assert (H2 : Nat.ltb v (c2+c) = true) by (apply Nat.ltb_lt; lia).
    assert (H3 : Nat.ltb v (c2+S c) = true) by (apply Nat.ltb_lt; lia).
    cbn [subst Nat.pred]. rewrite H1, H3. cbn [subst Nat.pred]. rewrite H2, H1. reflexivity.
  - subst v.
    assert (H1 : Nat.ltb c2 c2 = false) by (apply Nat.ltb_ge; lia).
    assert (He : Nat.eqb c2 c2 = true) by (apply Nat.eqb_eq; reflexivity).
    assert (H3 : Nat.ltb c2 (c2+S c) = true) by (apply Nat.ltb_lt; lia).
    cbn [subst Nat.pred]. rewrite H1, He, H3.
    rewrite (subst_lift_offset w u c2 0 c) by lia.
    cbn [subst Nat.pred]. rewrite H1, He. reflexivity.
  - destruct v as [|y]; [lia |]. cbn [Nat.pred].
    destruct (Nat.lt_trichotomy y (c2+c)) as [Hq | [Hq | Hq]].
    + assert (H1 : Nat.ltb (S y) c2 = false) by (apply Nat.ltb_ge; lia).
      assert (He : Nat.eqb (S y) c2 = false) by (apply Nat.eqb_neq; lia).
      assert (H2 : Nat.ltb y (c2+c) = true) by (apply Nat.ltb_lt; lia).
      assert (H3 : Nat.ltb (S y) (c2+S c) = true) by (apply Nat.ltb_lt; lia).
      cbn [subst Nat.pred]. rewrite H1, He, H3. cbn [subst Nat.pred]. rewrite H2, H1, He.
      reflexivity.
    + subst y.
      assert (H1 : Nat.ltb (S (c2+c)) c2 = false) by (apply Nat.ltb_ge; lia).
      assert (He : Nat.eqb (S (c2+c)) c2 = false) by (apply Nat.eqb_neq; lia).
      assert (H2 : Nat.ltb (c2+c) (c2+c) = false) by (apply Nat.ltb_ge; lia).
      assert (He2 : Nat.eqb (c2+c) (c2+c) = true) by (apply Nat.eqb_eq; reflexivity).
      assert (H3 : Nat.ltb (S (c2+c)) (c2+S c) = false) by (apply Nat.ltb_ge; lia).
      assert (He3 : Nat.eqb (S (c2+c)) (c2+S c) = true) by (apply Nat.eqb_eq; lia).
      cbn [subst Nat.pred]. rewrite H1, He, H3, He3. cbn [subst Nat.pred]. rewrite H2, He2.
      replace (lift (c2+S c) 0 u) with (lift 1 c2 (lift (c2+c) 0 u)).
      * rewrite subst_lift_cancel. reflexivity.
      * rewrite lift_fuse_zero by lia. f_equal. lia.
    + assert (H1 : Nat.ltb (S y) c2 = false) by (apply Nat.ltb_ge; lia).
      assert (He : Nat.eqb (S y) c2 = false) by (apply Nat.eqb_neq; lia).
      assert (H2 : Nat.ltb y (c2+c) = false) by (apply Nat.ltb_ge; lia).
      assert (He2 : Nat.eqb y (c2+c) = false) by (apply Nat.eqb_neq; lia).
      assert (H3 : Nat.ltb (S y) (c2+S c) = false) by (apply Nat.ltb_ge; lia).
      assert (He3 : Nat.eqb (S y) (c2+S c) = false) by (apply Nat.eqb_neq; lia).
      assert (H4 : Nat.ltb y c2 = false) by (apply Nat.ltb_ge; lia).
      assert (He4 : Nat.eqb y c2 = false) by (apply Nat.eqb_neq; lia).
      cbn [subst Nat.pred]. rewrite H1, He, H3, He3. cbn [subst Nat.pred].
      rewrite H2, He2, H4, He4. reflexivity.
Qed.

Lemma subst_subst_comm : forall t u w c c2,
    subst u (c2+c) (subst w c2 t) =
    subst (subst u c w) c2 (subst u (c2+S c) t).
Proof.
  induction t; intros u w c c2;
    try solve [apply subst_subst_comm_var];
    cbn; try reflexivity; f_equal; auto;
    try solve [
      replace (S (c2+c)) with (S c2+c) by lia;
      replace (S (c2+S c)) with (S c2+S c) by lia; auto].
Qed.

Corollary subst_subst_zero_comm : forall t u w c,
    subst u c (subst w 0 t) =
    subst (subst u c w) 0 (subst u (S c) t).
Proof.
  intros t u w c.
  replace c with (0+c) at 1 by lia. replace (S c) with (0+S c) by lia.
  apply subst_subst_comm.
Qed.

Lemma lift_subst_comm_var : forall v w d c c2,
    lift d (c+c2) (subst w c2 (TVar v)) =
    subst (lift d c w) c2 (lift d (S c+c2) (TVar v)).
Proof.
  intros v w d c c2.
  destruct (Nat.lt_trichotomy v c2) as [Hlt | [Heq | Hgt]].
  - assert (H1 : Nat.ltb v c2 = true) by (apply Nat.ltb_lt; lia).
    assert (H2 : Nat.ltb v (c+c2) = true) by (apply Nat.ltb_lt; lia).
    assert (H3 : Nat.ltb v (S c+c2) = true) by (apply Nat.ltb_lt; lia).
    cbn [subst lift Nat.pred]. rewrite H1, H3. cbn [subst lift Nat.pred]. rewrite H1, H2.
    reflexivity.
  - subst v.
    assert (H1 : Nat.ltb c2 c2 = false) by (apply Nat.ltb_ge; lia).
    assert (He : Nat.eqb c2 c2 = true) by (apply Nat.eqb_eq; reflexivity).
    assert (H3 : Nat.ltb c2 (S c+c2) = true) by (apply Nat.ltb_lt; lia).
    cbn [subst lift Nat.pred]. rewrite H1, He, H3. cbn [subst Nat.pred]. rewrite H1, He.
    rewrite Nat.add_comm. apply lift_lift_comm; lia.
  - assert (H1 : Nat.ltb v c2 = false) by (apply Nat.ltb_ge; lia).
    assert (He : Nat.eqb v c2 = false) by (apply Nat.eqb_neq; lia).
    destruct v as [|y]; [lia |]. cbn [Nat.pred].
    destruct (Nat.ltb y (c+c2)) eqn:Hq.
    + apply Nat.ltb_lt in Hq.
      assert (H3 : Nat.ltb (S y) (S c+c2) = true) by (apply Nat.ltb_lt; lia).
      assert (Hj : Nat.ltb (S y) c2 = false) by (apply Nat.ltb_ge; lia).
      assert (Hej : Nat.eqb (S y) c2 = false) by (apply Nat.eqb_neq; lia).
      cbn [subst lift Nat.pred]. rewrite H1, He, H3. cbn [subst lift Nat.pred].
      rewrite Hj, Hej. rewrite <- Nat.ltb_lt in Hq. rewrite Hq. reflexivity.
    + apply Nat.ltb_ge in Hq.
      assert (H3 : Nat.ltb (S y) (S c+c2) = false) by (apply Nat.ltb_ge; lia).
      assert (Hdj : Nat.ltb (d+S y) c2 = false) by (apply Nat.ltb_ge; lia).
      assert (Hedj : Nat.eqb (d+S y) c2 = false) by (apply Nat.eqb_neq; lia).
      cbn [subst lift Nat.pred]. rewrite H1, He, H3. cbn [subst lift Nat.pred].
      rewrite Hdj, Hedj. rewrite <- Nat.ltb_ge in Hq. rewrite Hq.
      f_equal. destruct d; cbn; lia.
Qed.

Lemma lift_subst_comm : forall t w d c c2,
    lift d (c2+c) (subst w c2 t) =
    subst (lift d c w) c2 (lift d (c2+S c) t).
Proof.
  induction t; intros w d c c2;
    try solve [rewrite Nat.add_comm;
      replace (c2 + S c) with (S c + c2) by lia;
      apply lift_subst_comm_var];
    cbn; try reflexivity; f_equal; auto;
    try solve [
      replace (S (c2+c)) with (S c2+c) by lia;
      replace (S (c2+S c)) with (S c2+S c) by lia; auto].
Qed.

Corollary lift_subst_zero_comm : forall t w d c,
    lift d c (subst w 0 t) = subst (lift d c w) 0 (lift d (S c) t).
Proof.
  intros t w d c.
  replace c with (0+c) at 1 by lia. replace (S c) with (0+S c) by lia.
  apply lift_subst_comm.
Qed.

(* Eta-specific binding facts. *)


Lemma subst_eta_beta_cancel_var : forall v c,
    subst (TVar 0) c (lift 1 (S c) (TVar v)) = TVar v.
Proof.
  intros v c. cbn [lift].
  destruct (Nat.ltb v (S c)) eqn:Hn.
  - apply Nat.ltb_lt in Hn. cbn [subst Nat.pred].
    destruct (Nat.eq_dec v c) as [->|Hneq].
    + rewrite Nat.ltb_irrefl, Nat.eqb_refl. cbn [lift].
      replace (c + 0) with c by lia. reflexivity.
    + assert (Hlt : Nat.ltb v c = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt. reflexivity.
  - apply Nat.ltb_ge in Hn. cbn [subst Nat.pred].
    assert (Hlt : Nat.ltb (1+v) c = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb (1+v) c = false) by (apply Nat.eqb_neq; lia).
    rewrite Hlt, Heq. f_equal.
Qed.

Lemma subst_eta_beta_cancel_gen : forall t c,
    subst (TVar 0) c (lift 1 (S c) t) = t.
Proof.
  induction t; intros c; try solve [apply subst_eta_beta_cancel_var];
    cbn; try reflexivity; f_equal; auto.
Qed.

Corollary subst_eta_beta_cancel : forall t,
    subst (TVar 0) 0 (lift 1 1 t) = t.
Proof. intros t. apply subst_eta_beta_cancel_gen. Qed.

Ltac nullary :=
  match goal with
  | |- exists u, ?L = lift 1 _ u /\ _ => exists L; cbn [lift]; auto
  end.

