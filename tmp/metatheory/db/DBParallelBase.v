(* ========================================================================== *)
(* Progress for the revised open-signature calculus (OpenSignaturesCore).     *)
(*                                                                            *)
(* The theorem proved here is exactly the [progress] statement of             *)
(* OpenSignaturesTheorems.v:                                                  *)
(*                                                                            *)
(*   forall t A, typing [] t A -> value t \/ exists u, step t u.              *)
(*                                                                            *)
(* Route.  Declarative typing converts freely (ty_conv), so the closed        *)
(* canonical-forms lemma needs conversion to preserve rigid weak-head        *)
(* shapes.  We follow the architecture of the earlier signature-pair         *)
(* development: parallel beta/computation reduction with a                   *)
(* complete development (Takahashi), parallel eta reduction with its own     *)
(* diamond, a Hindley-Rosen commutation of the two, and joinability of       *)
(* conversion.  The small generic closure library below is self-contained;   *)
(* everything about the term language is proved specifically for the revised *)
(* calculus.                                                                 *)
(* ========================================================================== *)

From Stdlib Require Import List Arith Lia PeanoNat String.
Import ListNotations.
Require Export ProofDB.DBCore.

(* ------------------------------------------------------------------ *)
(*  Generic relation closures                                         *)
(* ------------------------------------------------------------------ *)

Inductive rtc {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
| rtc_refl : forall x, rtc R x x
| rtc_step : forall x y z, R x y -> rtc R y z -> rtc R x z.

Arguments rtc_refl {X R x}.
Arguments rtc_step {X R x y z} _ _.

Lemma rtc_one : forall X (R : X -> X -> Prop) x y,
    R x y -> rtc R x y.
Proof. intros X R x y H. eapply rtc_step; [exact H | apply rtc_refl]. Qed.

Lemma rtc_trans : forall X (R : X -> X -> Prop) x y z,
    rtc R x y -> rtc R y z -> rtc R x z.
Proof.
  intros X R x y z Hxy Hyz. induction Hxy; eauto using rtc.
  
Qed.

Definition diamond {X : Type} (R : X -> X -> Prop) : Prop :=
  forall x y z, R x y -> R x z -> exists w, R y w /\ R z w.

Definition confluent {X : Type} (R : X -> X -> Prop) : Prop :=
  forall x y z, rtc R x y -> rtc R x z ->
    exists w, rtc R y w /\ rtc R z w.

Lemma diamond_rtc_strip : forall X (R : X -> X -> Prop),
    diamond R -> forall x y z,
    rtc R x y -> R x z -> exists w, rtc R y w /\ rtc R z w.
Proof.
  intros X R HD x y z Hxy. revert z.
  induction Hxy as [x | x x1 y Hxx1 Hx1y IH]; intros z Hxz.
  - exists z. split; [apply rtc_one; exact Hxz | apply rtc_refl].
  - destruct (HD x x1 z Hxx1 Hxz) as [q [Hx1q Hzq]].
    destruct (IH q Hx1q) as [w [Hyw Hqw]].
    exists w. split; [exact Hyw | eapply rtc_step; eassumption].
Qed.

Lemma diamond_rtc_confluent : forall X (R : X -> X -> Prop),
    diamond R -> confluent R.
Proof.
  intros X R HD x y z Hxy. revert z.
  induction Hxy as [x | x x1 y Hxx1 Hx1y IH]; intros z Hxz.
  - exists z. split; [exact Hxz | apply rtc_refl].
  - destruct (diamond_rtc_strip X R HD x z x1 Hxz Hxx1)
      as [q [Hzq Hx1q]].
    destruct (IH q Hx1q) as [w [Hyw Hqw]].
    exists w. split; [exact Hyw | eapply rtc_trans; eassumption].
Qed.

Lemma rtc_map_rel : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> Y),
    (forall x y, R x y -> S (F x) (F y)) ->
    forall x y, rtc R x y -> rtc S (F x) (F y).
Proof.
  intros X Y R S F HF x y H. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply HF; exact H | exact IHrtc].
Qed.

(* ------------------------------------------------------------------ *)
(*  Term size                                                          *)
(* ------------------------------------------------------------------ *)

Fixpoint tsize (t : term) : nat :=
  match t with
  | TVar _ | TSort _ | TUnitT | TUnit | TUId | TTag _ | TEnumU | TNilE
  | TEZero | TI1 | TIBot => 1
  | TLam b => S (tsize b)
  | TFst p | TSnd p => S (tsize p)
  | TEnumT E => S (tsize E)
  | TESucc n => S (tsize n)
  | TIDesc IT => S (tsize IT)
  | TIVar i => S (tsize i)
  | TIn x => S (tsize x)
  | TPi a b | TApp a b | TSigma a b | TPair a b | TConsE a b | TEPi _ a b
  | TIProd a b | TIPi a b | TISig a b | TIChoice a b | TMuI a b =>
      S (tsize a + tsize b)
  | TInterp a b c | TClose a b c => S (tsize a + tsize b + tsize c)
  | TSwitch _ a b c d => S (tsize a + tsize b + tsize c + tsize d)
  | TIAll a b c d e => S (tsize a + tsize b + tsize c + tsize d + tsize e)
  | TInd a b c d e f | THyps a b c d e f =>
      S (tsize a + tsize b + tsize c + tsize d + tsize e + tsize f)
  | TCloseCase _ a b c d e f g | TCloseInd a b c d e f g =>
      S (tsize a + tsize b + tsize c + tsize d + tsize e + tsize f + tsize g)
  end.

Lemma tsize_pos : forall t, 1 <= tsize t.
Proof. destruct t; cbn; lia. Qed.

Lemma tsize_strong_ind : forall (P : term -> Prop),
    (forall t, (forall u, tsize u < tsize t -> P u) -> P t) ->
    forall t, P t.
Proof.
  intros P H t.
  refine (@well_founded_induction nat lt lt_wf
            (fun n => forall u, tsize u = n -> P u)
            _ (tsize t) t eq_refl).
  intros n IH u Hu. apply H. intros v Hv. eapply IH; [|reflexivity]. lia.
Qed.

Lemma tsize_lift : forall t d c, tsize (lift d c t) = tsize t.
Proof.
  induction t; intros d c;
    try solve [cbn [lift]; destruct (Nat.ltb n c); reflexivity];
    cbn; auto;
    repeat match goal with
    | IH : forall d c, tsize (lift d c ?x) = tsize ?x
      |- context [tsize (lift ?d ?c ?x)] => rewrite (IH d c)
    end; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Lifting and substitution algebra                                   *)
(* ------------------------------------------------------------------ *)

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

Lemma subst_eta_app : forall f w,
    subst w 0 (TApp (lift 1 0 f) (TVar 0)) = TApp f w.
Proof.
  intros f w. cbn [subst Nat.pred]. rewrite subst_lift_zero, lift_zero_id. reflexivity.
Qed.

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

Lemma lift_one_injective : forall x c y, lift 1 c x = lift 1 c y -> x = y.
Proof.
  induction x; intros c y H; destruct y; cbn [lift] in H;
    try solve [
      repeat match type of H with
      | context [Nat.ltb ?a ?b] => destruct (Nat.ltb a b) eqn:?
      end; try discriminate];
    inversion H; subst; try reflexivity;
    try solve [
      repeat match type of H with
      | context [Nat.ltb ?a ?b] => destruct (Nat.ltb a b) eqn:?
      end; try discriminate; inversion H;
      repeat match goal with
      | Hlt : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in Hlt
      | Hlt : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in Hlt
      end; f_equal; lia];
    f_equal; eauto.
Qed.

(* A term in the images of both [lift 1 i] and [lift 1 j] (j < i) is in
   the image of their composite. *)
Lemma lift_factor : forall g r c1 c2, c2 < c1 ->
    lift 1 c1 g = lift 1 c2 r ->
    exists u, g = lift 1 c2 u /\ r = lift 1 (Nat.pred c1) u.
Proof.
  induction g; intros r c1 c2 Hji H; destruct r; cbn [lift] in H;
    try solve [
      repeat match type of H with
      | context [Nat.ltb ?a ?b] => destruct (Nat.ltb a b) eqn:?
      end; discriminate].
  - (* variables *)
    destruct (Nat.ltb n c1) eqn:Hni; destruct (Nat.ltb n0 c2) eqn:Hn0j;
      inversion H; subst;
      repeat match goal with
      | Hlt : Nat.ltb _ _ = true |- _ => apply Nat.ltb_lt in Hlt
      | Hlt : Nat.ltb _ _ = false |- _ => apply Nat.ltb_ge in Hlt
      end.
    + exists (TVar n0). cbn [lift].
      assert (Hlt : Nat.ltb n0 c2 = true) by (apply Nat.ltb_lt; lia).
      assert (Hlt2 : Nat.ltb n0 (Nat.pred c1) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt, Hlt2. auto.
    + exists (TVar n0). cbn [lift].
      assert (Hlt : Nat.ltb n0 c2 = false) by (apply Nat.ltb_ge; lia).
      assert (Hlt2 : Nat.ltb n0 (Nat.pred c1) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt, Hlt2. auto.
    + lia.
    + match goal with
      | |- exists _, TVar ?m = _ /\ _ => exists (TVar (Nat.pred m))
      end. cbn [lift].
      match goal with
      | |- context [Nat.ltb (Nat.pred ?m) c2] =>
        assert (Hlt : Nat.ltb (Nat.pred m) c2 = false) by (apply Nat.ltb_ge; lia);
        assert (Hlt2 : Nat.ltb (Nat.pred m) (Nat.pred c1) = false)
          by (apply Nat.ltb_ge; lia)
      end.
      rewrite Hlt, Hlt2. split; f_equal; lia.
  - inversion H; subst. nullary.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ (S c1) (S c2) ltac:(lia) H2) as [u2 [E2 F2]].
    exists (TPi u1 u2). cbn [lift]. subst.
    replace (S (Nat.pred c1)) with (Nat.pred (S c1)) by lia. auto.
  - inversion H; subst.
    destruct (IHg _ (S c1) (S c2) ltac:(lia) H1) as [u [E F]].
    exists (TLam u). cbn [lift]. subst.
    replace (S (Nat.pred c1)) with (Nat.pred (S c1)) by lia. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    exists (TApp u1 u2). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ (S c1) (S c2) ltac:(lia) H2) as [u2 [E2 F2]].
    exists (TSigma u1 u2). cbn [lift]. subst.
    replace (S (Nat.pred c1)) with (Nat.pred (S c1)) by lia. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    exists (TPair u1 u2). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg _ _ _ Hji H1) as [u [E F]].
    exists (TFst u). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg _ _ _ Hji H1) as [u [E F]].
    exists (TSnd u). cbn [lift]. subst. auto.
  - nullary.
  - nullary.
  - nullary.
  - inversion H; subst. nullary.
  - nullary.
  - nullary.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    exists (TConsE u1 u2). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg _ _ _ Hji H1) as [u [E F]].
    exists (TEnumT u). cbn [lift]. subst. auto.
  - nullary.
  - inversion H; subst.
    destruct (IHg _ _ _ Hji H1) as [u [E F]].
    exists (TESucc u). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H2) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H3) as [u2 [E2 F2]].
    exists (TEPi k0 u1 u2). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H2) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H3) as [u2 [E2 F2]].
    destruct (IHg3 _ _ _ Hji H4) as [u3 [E3 F3]].
    destruct (IHg4 _ _ _ Hji H5) as [u4 [E4 F4]].
    exists (TSwitch k0 u1 u2 u3 u4). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg _ _ _ Hji H1) as [u [E F]].
    exists (TIDesc u). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg _ _ _ Hji H1) as [u [E F]].
    exists (TIVar u). cbn [lift]. subst. auto.
  - nullary.
  - nullary.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    exists (TIProd u1 u2). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    exists (TIPi u1 u2). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    exists (TISig u1 u2). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    exists (TIChoice u1 u2). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    destruct (IHg3 _ _ _ Hji H3) as [u3 [E3 F3]].
    exists (TInterp u1 u2 u3). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    exists (TMuI u1 u2). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg _ _ _ Hji H1) as [u [E F]].
    exists (TIn u). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    destruct (IHg3 _ _ _ Hji H3) as [u3 [E3 F3]].
    destruct (IHg4 _ _ _ Hji H4) as [u4 [E4 F4]].
    destruct (IHg5 _ _ _ Hji H5) as [u5 [E5 F5]].
    destruct (IHg6 _ _ _ Hji H6) as [u6 [E6 F6]].
    exists (TInd u1 u2 u3 u4 u5 u6). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    destruct (IHg3 _ _ _ Hji H3) as [u3 [E3 F3]].
    destruct (IHg4 _ _ _ Hji H4) as [u4 [E4 F4]].
    destruct (IHg5 _ _ _ Hji H5) as [u5 [E5 F5]].
    exists (TIAll u1 u2 u3 u4 u5). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    destruct (IHg3 _ _ _ Hji H3) as [u3 [E3 F3]].
    destruct (IHg4 _ _ _ Hji H4) as [u4 [E4 F4]].
    destruct (IHg5 _ _ _ Hji H5) as [u5 [E5 F5]].
    destruct (IHg6 _ _ _ Hji H6) as [u6 [E6 F6]].
    exists (THyps u1 u2 u3 u4 u5 u6). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    destruct (IHg3 _ _ _ Hji H3) as [u3 [E3 F3]].
    exists (TClose u1 u2 u3). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H2) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H3) as [u2 [E2 F2]].
    destruct (IHg3 _ _ _ Hji H4) as [u3 [E3 F3]].
    destruct (IHg4 _ _ _ Hji H5) as [u4 [E4 F4]].
    destruct (IHg5 _ _ _ Hji H6) as [u5 [E5 F5]].
    destruct (IHg6 _ _ _ Hji H7) as [u6 [E6 F6]].
    destruct (IHg7 _ _ _ Hji H8) as [u7 [E7 F7]].
    exists (TCloseCase k0 u1 u2 u3 u4 u5 u6 u7). cbn [lift]. subst. auto.
  - inversion H; subst.
    destruct (IHg1 _ _ _ Hji H1) as [u1 [E1 F1]].
    destruct (IHg2 _ _ _ Hji H2) as [u2 [E2 F2]].
    destruct (IHg3 _ _ _ Hji H3) as [u3 [E3 F3]].
    destruct (IHg4 _ _ _ Hji H4) as [u4 [E4 F4]].
    destruct (IHg5 _ _ _ Hji H5) as [u5 [E5 F5]].
    destruct (IHg6 _ _ _ Hji H6) as [u6 [E6 F6]].
    destruct (IHg7 _ _ _ Hji H7) as [u7 [E7 F7]].
    exists (TCloseInd u1 u2 u3 u4 u5 u6 u7). cbn [lift]. subst. auto.
Qed.

(* The shape of a lifted eta-redex. *)
Lemma lift_eta_shape_decomp_k : forall f r c,
    lift 1 c f = TLam (TApp (lift 1 0 r) (TVar 0)) ->
    exists u, r = lift 1 c u /\ f = TLam (TApp (lift 1 0 u) (TVar 0)).
Proof.
  intros f r c Heq.
  destruct f; cbn [lift] in Heq; try discriminate.
  - destruct (Nat.ltb n c); discriminate.
  - inversion Heq; subst.
    destruct f; cbn [lift] in H0; try discriminate.
    + destruct (Nat.ltb n (S c)); discriminate.
    + inversion H0; subst.
      assert (Harg : lift 1 (S c) f2 = lift 1 (S c) (TVar 0)) by
        (rewrite H2; reflexivity).
      apply lift_one_injective in Harg. subst f2.
      destruct (lift_factor f1 r (S c) 0 ltac:(lia) H1) as [u [E F]].
      cbn [Nat.pred] in F. subst. exists u. auto.
Qed.

(* ------------------------------------------------------------------ *)
(*  Parallel beta/computation reduction                                *)
(* ------------------------------------------------------------------ *)

(* Congruence rules come first, then the root contractions with every
   metavariable developed in parallel.  Right-hand sides are written in
   the normal form that [cbn] produces from [root_step]. *)
Inductive pstep : term -> term -> Prop :=
| ps_TVar : forall n, pstep (TVar n) (TVar n)
| ps_TSort : forall k, pstep (TSort k) (TSort k)
| ps_TPi : forall A A' B B', pstep A A' -> pstep B B' -> pstep (TPi A B) (TPi A' B')
| ps_TLam : forall b b', pstep b b' -> pstep (TLam b) (TLam b')
| ps_TApp : forall f f' a a', pstep f f' -> pstep a a' -> pstep (TApp f a) (TApp f' a')
| ps_TSigma : forall A A' B B', pstep A A' -> pstep B B' -> pstep (TSigma A B) (TSigma A' B')
| ps_TPair : forall a a' b b', pstep a a' -> pstep b b' -> pstep (TPair a b) (TPair a' b')
| ps_TFst : forall p p', pstep p p' -> pstep (TFst p) (TFst p')
| ps_TSnd : forall p p', pstep p p' -> pstep (TSnd p) (TSnd p')
| ps_TUnitT : pstep TUnitT TUnitT
| ps_TUnit : pstep TUnit TUnit
| ps_TUId : pstep TUId TUId
| ps_TTag : forall s, pstep (TTag s) (TTag s)
| ps_TEnumU : pstep TEnumU TEnumU
| ps_TNilE : pstep TNilE TNilE
| ps_TConsE : forall tag tag' E E', pstep tag tag' -> pstep E E' -> pstep (TConsE tag E) (TConsE tag' E')
| ps_TEnumT : forall E E', pstep E E' -> pstep (TEnumT E) (TEnumT E')
| ps_TEZero : pstep TEZero TEZero
| ps_TESucc : forall n n', pstep n n' -> pstep (TESucc n) (TESucc n')
| ps_TEPi : forall k E E' P P', pstep E E' -> pstep P P' -> pstep (TEPi k E P) (TEPi k E' P')
| ps_TSwitch : forall k E E' P P' p p' e e', pstep E E' -> pstep P P' -> pstep p p' -> pstep e e' -> pstep (TSwitch k E P p e) (TSwitch k E' P' p' e')
| ps_TIDesc : forall IT IT', pstep IT IT' -> pstep (TIDesc IT) (TIDesc IT')
| ps_TIVar : forall i i', pstep i i' -> pstep (TIVar i) (TIVar i')
| ps_TI1 : pstep TI1 TI1
| ps_TIBot : pstep TIBot TIBot
| ps_TIProd : forall A A' B B', pstep A A' -> pstep B B' -> pstep (TIProd A B) (TIProd A' B')
| ps_TIPi : forall A A' D D', pstep A A' -> pstep D D' -> pstep (TIPi A D) (TIPi A' D')
| ps_TISig : forall A A' D D', pstep A A' -> pstep D D' -> pstep (TISig A D) (TISig A' D')
| ps_TIChoice : forall E E' D D', pstep E E' -> pstep D D' -> pstep (TIChoice E D) (TIChoice E' D')
| ps_TInterp : forall IT IT' D D' X X', pstep IT IT' -> pstep D D' -> pstep X X' -> pstep (TInterp IT D X) (TInterp IT' D' X')
| ps_TMuI : forall IT IT' D D', pstep IT IT' -> pstep D D' -> pstep (TMuI IT D) (TMuI IT' D')
| ps_TIn : forall x x', pstep x x' -> pstep (TIn x) (TIn x')
| ps_TInd : forall IT IT' D D' P P' s s' i i' x x', pstep IT IT' -> pstep D D' -> pstep P P' -> pstep s s' -> pstep i i' -> pstep x x' -> pstep (TInd IT D P s i x) (TInd IT' D' P' s' i' x')
| ps_TIAll : forall IT IT' D D' X X' x x' P P', pstep IT IT' -> pstep D D' -> pstep X X' -> pstep x x' -> pstep P P' -> pstep (TIAll IT D X x P) (TIAll IT' D' X' x' P')
| ps_THyps : forall IT IT' D D' X X' P P' h h' x x', pstep IT IT' -> pstep D D' -> pstep X X' -> pstep P P' -> pstep h h' -> pstep x x' -> pstep (THyps IT D X P h x) (THyps IT' D' X' P' h' x')
| ps_TClose : forall IT IT' F F' G G', pstep IT IT' -> pstep F F' -> pstep G G' -> pstep (TClose IT F G) (TClose IT' F' G')
| ps_TCloseCase : forall k IT IT' F F' G G' i i' Q Q' b b' x x', pstep IT IT' -> pstep F F' -> pstep G G' -> pstep i i' -> pstep Q Q' -> pstep b b' -> pstep x x' -> pstep (TCloseCase k IT F G i Q b x) (TCloseCase k IT' F' G' i' Q' b' x')
| ps_TCloseInd : forall IT IT' G G' P P' s s' F F' i i' x x', pstep IT IT' -> pstep G G' -> pstep P P' -> pstep s s' -> pstep F F' -> pstep i i' -> pstep x x' -> pstep (TCloseInd IT G P s F i x) (TCloseInd IT' G' P' s' F' i' x')

| ps_beta : forall b b' a a', pstep b b' -> pstep a a' ->
    pstep (TApp (TLam b) a) (subst a' 0 b')
| ps_fst_pair : forall a a' b, pstep a a' -> pstep (TFst (TPair a b)) a'
| ps_snd_pair : forall a b b', pstep b b' -> pstep (TSnd (TPair a b)) b'
| ps_epi_nil : forall k P, pstep (TEPi k TNilE P) TUnitT
| ps_epi_cons : forall k tag E E' P P', pstep E E' -> pstep P P' ->
    pstep (TEPi k (TConsE tag E) P)
      (TSigma (TApp P' TEZero)
        (TEPi k (lift 1 0 E')
          (TLam (TApp (lift 2 0 P') (TESucc (TVar 0))))))
| ps_switch_zero : forall k tag E P p p' ps, pstep p p' ->
    pstep (TSwitch k (TConsE tag E) P (TPair p ps) TEZero) p'
| ps_switch_succ : forall k tag E E' P P' p ps ps' n n',
    pstep E E' -> pstep P P' -> pstep ps ps' -> pstep n n' ->
    pstep (TSwitch k (TConsE tag E) P (TPair p ps) (TESucc n))
      (TSwitch k E' (TLam (TApp (lift 1 0 P') (TESucc (TVar 0)))) ps' n')
| ps_interp_var : forall IT i i' X X', pstep i i' -> pstep X X' ->
    pstep (TInterp IT (TIVar i) X) (TApp X' i')
| ps_interp_one : forall IT X, pstep (TInterp IT TI1 X) TUnitT
| ps_interp_bot : forall IT X, pstep (TInterp IT TIBot X) (TEnumT TNilE)
| ps_interp_prod : forall IT IT' A A' B B' X X',
    pstep IT IT' -> pstep A A' -> pstep B B' -> pstep X X' ->
    pstep (TInterp IT (TIProd A B) X)
      (TSigma (TInterp IT' A' X')
        (TInterp (lift 1 0 IT') (lift 1 0 B') (lift 1 0 X')))
| ps_interp_pi : forall IT IT' A A' D D' X X',
    pstep IT IT' -> pstep A A' -> pstep D D' -> pstep X X' ->
    pstep (TInterp IT (TIPi A D) X)
      (TPi A' (TInterp (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
        (lift 1 0 X')))
| ps_interp_sig : forall IT IT' A A' D D' X X',
    pstep IT IT' -> pstep A A' -> pstep D D' -> pstep X X' ->
    pstep (TInterp IT (TISig A D) X)
      (TSigma A' (TInterp (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
        (lift 1 0 X')))
| ps_interp_choice : forall IT IT' E E' D D' X X',
    pstep IT IT' -> pstep E E' -> pstep D D' -> pstep X X' ->
    pstep (TInterp IT (TIChoice E D) X)
      (TSigma (TEnumT E')
        (TInterp (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
          (lift 1 0 X')))
| ps_iall_var : forall IT i i' X x x' P P',
    pstep i i' -> pstep x x' -> pstep P P' ->
    pstep (TIAll IT (TIVar i) X x P) (TApp P' (TPair i' x'))
| ps_iall_one : forall IT X P, pstep (TIAll IT TI1 X TUnit P) TUnitT
| ps_iall_bot : forall IT X x P, pstep (TIAll IT TIBot X x P) TUnitT
| ps_iall_prod : forall IT IT' A A' B B' X X' a a' b b' P P',
    pstep IT IT' -> pstep A A' -> pstep B B' -> pstep X X' ->
    pstep a a' -> pstep b b' -> pstep P P' ->
    pstep (TIAll IT (TIProd A B) X (TPair a b) P)
      (TSigma (TIAll IT' A' X' a' P')
        (TIAll (lift 1 0 IT') (lift 1 0 B') (lift 1 0 X') (lift 1 0 b')
          (lift 1 0 P')))
| ps_iall_pi : forall IT IT' A A' D D' X X' f f' P P',
    pstep IT IT' -> pstep A A' -> pstep D D' -> pstep X X' ->
    pstep f f' -> pstep P P' ->
    pstep (TIAll IT (TIPi A D) X f P)
      (TPi A' (TIAll (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
        (lift 1 0 X') (TApp (lift 1 0 f') (TVar 0)) (lift 1 0 P')))
| ps_iall_sig : forall IT IT' A D D' X X' a a' x x' P P',
    pstep IT IT' -> pstep D D' -> pstep X X' ->
    pstep a a' -> pstep x x' -> pstep P P' ->
    pstep (TIAll IT (TISig A D) X (TPair a x) P)
      (TIAll IT' (TApp D' a') X' x' P')
| ps_iall_choice : forall IT IT' E D D' X X' e e' x x' P P',
    pstep IT IT' -> pstep D D' -> pstep X X' ->
    pstep e e' -> pstep x x' -> pstep P P' ->
    pstep (TIAll IT (TIChoice E D) X (TPair e x) P)
      (TIAll IT' (TApp D' e') X' x' P')
| ps_hyps_var : forall IT i i' X P h h' x x',
    pstep i i' -> pstep h h' -> pstep x x' ->
    pstep (THyps IT (TIVar i) X P h x) (TApp (TApp h' i') x')
| ps_hyps_one : forall IT X P h, pstep (THyps IT TI1 X P h TUnit) TUnit
| ps_hyps_bot : forall IT X P h x, pstep (THyps IT TIBot X P h x) TUnit
| ps_hyps_prod : forall IT IT' A A' B B' X X' P P' h h' a a' b b',
    pstep IT IT' -> pstep A A' -> pstep B B' -> pstep X X' -> pstep P P' ->
    pstep h h' -> pstep a a' -> pstep b b' ->
    pstep (THyps IT (TIProd A B) X P h (TPair a b))
      (TPair (THyps IT' A' X' P' h' a') (THyps IT' B' X' P' h' b'))
| ps_hyps_pi : forall IT IT' A D D' X X' P P' h h' f f',
    pstep IT IT' -> pstep D D' -> pstep X X' -> pstep P P' ->
    pstep h h' -> pstep f f' ->
    pstep (THyps IT (TIPi A D) X P h f)
      (TLam (THyps (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
        (lift 1 0 X') (lift 1 0 P') (lift 1 0 h')
        (TApp (lift 1 0 f') (TVar 0))))
| ps_hyps_sig : forall IT IT' A D D' X X' P P' h h' a a' x x',
    pstep IT IT' -> pstep D D' -> pstep X X' -> pstep P P' ->
    pstep h h' -> pstep a a' -> pstep x x' ->
    pstep (THyps IT (TISig A D) X P h (TPair a x))
      (THyps IT' (TApp D' a') X' P' h' x')
| ps_hyps_choice : forall IT IT' E D D' X X' P P' h h' e e' x x',
    pstep IT IT' -> pstep D D' -> pstep X X' -> pstep P P' ->
    pstep h h' -> pstep e e' -> pstep x x' ->
    pstep (THyps IT (TIChoice E D) X P h (TPair e x))
      (THyps IT' (TApp D' e') X' P' h' x')
| ps_ind_red : forall IT IT' D D' P P' st st' i i' xs xs',
    pstep IT IT' -> pstep D D' -> pstep P P' -> pstep st st' ->
    pstep i i' -> pstep xs xs' ->
    pstep (TInd IT D P st i (TIn xs))
      (TApp (TApp (TApp st' i') xs')
        (THyps IT' (TApp D' i') (TMuI IT' D') P'
          (TLam (TLam (TInd (lift 2 0 IT') (lift 2 0 D') (lift 2 0 P')
            (lift 2 0 st') (TVar 1) (TVar 0)))) xs'))
| ps_closecase_red : forall k IT F G i Q b b' xs xs',
    pstep b b' -> pstep xs xs' ->
    pstep (TCloseCase k IT F G i Q b (TIn xs)) (TApp b' xs')
| ps_closeind_red : forall IT IT' G G' P P' st st' F F' i i' xs xs',
    pstep IT IT' -> pstep G G' -> pstep P P' -> pstep st st' ->
    pstep F F' -> pstep i i' -> pstep xs xs' ->
    pstep (TCloseInd IT G P st F i (TIn xs))
      (TApp (TApp (TApp (TApp st' F') i') xs')
        (THyps IT' (TApp F' i') (TClose IT' G' G')
          (TLam (TApp (TApp (TApp (lift 1 0 P') (lift 1 0 G'))
            (TFst (TVar 0))) (TSnd (TVar 0))))
          (TLam (TLam (TCloseInd (lift 2 0 IT') (lift 2 0 G')
            (lift 2 0 P') (lift 2 0 st') (lift 2 0 G')
            (TVar 1) (TVar 0)))) xs')).

#[local] Hint Constructors pstep : ps.

Lemma pstep_refl : forall t, pstep t t.
Proof. induction t; constructor; auto. Qed.
#[local] Hint Resolve pstep_refl : ps.

Ltac apply_root tac :=
  first
    [ eapply ps_beta; tac
    | eapply ps_fst_pair; tac
    | eapply ps_snd_pair; tac
    | eapply ps_epi_nil; tac
    | eapply ps_epi_cons; tac
    | eapply ps_switch_zero; tac
    | eapply ps_switch_succ; tac
    | eapply ps_interp_var; tac
    | eapply ps_interp_one; tac
    | eapply ps_interp_bot; tac
    | eapply ps_interp_prod; tac
    | eapply ps_interp_pi; tac
    | eapply ps_interp_sig; tac
    | eapply ps_interp_choice; tac
    | eapply ps_iall_var; tac
    | eapply ps_iall_one; tac
    | eapply ps_iall_bot; tac
    | eapply ps_iall_prod; tac
    | eapply ps_iall_pi; tac
    | eapply ps_iall_sig; tac
    | eapply ps_iall_choice; tac
    | eapply ps_hyps_var; tac
    | eapply ps_hyps_one; tac
    | eapply ps_hyps_bot; tac
    | eapply ps_hyps_prod; tac
    | eapply ps_hyps_pi; tac
    | eapply ps_hyps_sig; tac
    | eapply ps_hyps_choice; tac
    | eapply ps_ind_red; tac
    | eapply ps_closecase_red; tac
    | eapply ps_closeind_red; tac ].

(* Root contractions are parallel steps (with identity development). *)
Lemma lift_one_one_zero : forall t, lift 1 1 (lift 1 0 t) = lift 2 0 t.
Proof.
  intros t. change 1 with (0 + 1) at 2. rewrite lift_fuse by lia. reflexivity.
Qed.

Lemma root_pstep : forall t u, root_step t = Some u -> pstep t u.
Proof.
  intros t u H. destruct t; cbn in H; try discriminate;
    repeat match goal with
    | H : match ?x with _ => _ end = Some _ |- _ =>
        destruct x; try discriminate
    end;
    inversion H; subst; unfold product, Bot, carrier, diagonal_motive; cbn;
    repeat rewrite lift_one_one_zero;
    apply_root ltac:(apply pstep_refl).
Qed.

Lemma step_pstep : forall t u, step t u -> pstep t u.
Proof.
  intros t u H. induction H; try solve [apply root_pstep; assumption];
    constructor; auto with ps.
Qed.

Ltac lift_norm :=
  repeat rewrite lift_lift_one_one;
  repeat rewrite lift_lift_one_zero;
  repeat rewrite lift_lift_two_zero;
  repeat rewrite lift_subst_zero_comm.

Ltac subst_norm :=
  repeat rewrite subst_lift_one_one;
  repeat rewrite subst_lift_one_zero;
  repeat rewrite subst_lift_two_zero;
  repeat rewrite subst_subst_zero_comm.

Lemma pstep_lift : forall t u, pstep t u -> forall d c,
    pstep (lift d c t) (lift d c u).
Proof.
  intros t u H. induction H; intros d c; cbn;
    try solve [apply pstep_refl | constructor; auto];
    lift_norm; apply_root ltac:(auto).
Qed.
#[local] Hint Resolve pstep_lift : ps.

Ltac pstep_subst_var :=
  match goal with
  | Hu : pstep ?u ?u' |- pstep (subst ?u ?c (TVar ?n)) (subst ?u' ?c (TVar ?n)) =>
    cbn [subst];
    destruct (Nat.lt_trichotomy n c) as [Hnk | [Hnk | Hnk]];
    [ assert (Hlt : Nat.ltb n c = true) by (apply Nat.ltb_lt; lia);
      rewrite Hlt; apply pstep_refl
    | subst n;
      assert (Hlt : Nat.ltb c c = false) by (apply Nat.ltb_ge; lia);
      rewrite Hlt, Nat.eqb_refl; apply pstep_lift; exact Hu
    | assert (Hlt : Nat.ltb n c = false) by (apply Nat.ltb_ge; lia);
      assert (Heq : Nat.eqb n c = false) by (apply Nat.eqb_neq; lia);
      rewrite Hlt, Heq; apply pstep_refl ]
  end.

Lemma pstep_subst : forall t t', pstep t t' -> forall u u' c,
    pstep u u' -> pstep (subst u c t) (subst u' c t').
Proof.
  intros t t' H. induction H; intros u u' c Hu;
    try solve [pstep_subst_var];
    cbn; try solve [constructor; auto];
    subst_norm; apply_root ltac:(auto).
Qed.
#[local] Hint Resolve pstep_subst : ps.

(* ------------------------------------------------------------------ *)
(*  Complete development                                               *)
(* ------------------------------------------------------------------ *)

Fixpoint pdev (t : term) : term :=
  match t with
  | TVar n => TVar n | TSort k => TSort k
  | TPi A B => TPi (pdev A) (pdev B)
  | TLam b => TLam (pdev b)
  | TApp (TLam b) a => subst (pdev a) 0 (pdev b)
  | TApp f a => TApp (pdev f) (pdev a)
  | TSigma A B => TSigma (pdev A) (pdev B)
  | TPair a b => TPair (pdev a) (pdev b)
  | TFst (TPair a _) => pdev a
  | TFst p => TFst (pdev p)
  | TSnd (TPair _ b) => pdev b
  | TSnd p => TSnd (pdev p)
  | TUnitT => TUnitT | TUnit => TUnit | TUId => TUId | TTag s => TTag s
  | TEnumU => TEnumU | TNilE => TNilE
  | TConsE tg E => TConsE (pdev tg) (pdev E)
  | TEnumT E => TEnumT (pdev E)
  | TEZero => TEZero | TESucc n => TESucc (pdev n)
  | TEPi k TNilE _ => TUnitT
  | TEPi k (TConsE tg E) P =>
      TSigma (TApp (pdev P) TEZero)
        (TEPi k (lift 1 0 (pdev E))
          (TLam (TApp (lift 2 0 (pdev P)) (TESucc (TVar 0)))))
  | TEPi k E P => TEPi k (pdev E) (pdev P)
  | TSwitch k E P p e =>
      match E with
      | TConsE tag tail =>
          match p with
          | TPair head rest =>
              match e with
              | TEZero => pdev head
              | TESucc n => TSwitch k (pdev tail)
                  (TLam (TApp (lift 1 0 (pdev P)) (TESucc (TVar 0)))) (pdev rest) (pdev n)
              | _ => TSwitch k (pdev E) (pdev P) (pdev p) (pdev e)
              end
          | _ => TSwitch k (pdev E) (pdev P) (pdev p) (pdev e)
          end
      | _ => TSwitch k (pdev E) (pdev P) (pdev p) (pdev e)
      end
  | TIDesc IT => TIDesc (pdev IT)
  | TIVar i => TIVar (pdev i)
  | TI1 => TI1 | TIBot => TIBot
  | TIProd A B => TIProd (pdev A) (pdev B)
  | TIPi A D => TIPi (pdev A) (pdev D)
  | TISig A D => TISig (pdev A) (pdev D)
  | TIChoice E D => TIChoice (pdev E) (pdev D)
  | TInterp IT (TIVar i) X => TApp (pdev X) (pdev i)
  | TInterp IT TI1 X => TUnitT
  | TInterp IT TIBot X => TEnumT TNilE
  | TInterp IT (TIProd A B) X =>
      TSigma (TInterp (pdev IT) (pdev A) (pdev X))
        (TInterp (lift 1 0 (pdev IT)) (lift 1 0 (pdev B)) (lift 1 0 (pdev X)))
  | TInterp IT (TIPi A D) X =>
      TPi (pdev A)
        (TInterp (lift 1 0 (pdev IT)) (TApp (lift 1 0 (pdev D)) (TVar 0))
          (lift 1 0 (pdev X)))
  | TInterp IT (TISig A D) X =>
      TSigma (pdev A)
        (TInterp (lift 1 0 (pdev IT)) (TApp (lift 1 0 (pdev D)) (TVar 0))
          (lift 1 0 (pdev X)))
  | TInterp IT (TIChoice E D) X =>
      TSigma (TEnumT (pdev E))
        (TInterp (lift 1 0 (pdev IT)) (TApp (lift 1 0 (pdev D)) (TVar 0))
          (lift 1 0 (pdev X)))
  | TInterp IT D X => TInterp (pdev IT) (pdev D) (pdev X)
  | TMuI IT D => TMuI (pdev IT) (pdev D)
  | TIn x => TIn (pdev x)
  | TInd IT D P st i (TIn xs) =>
      TApp (TApp (TApp (pdev st) (pdev i)) (pdev xs))
        (THyps (pdev IT) (TApp (pdev D) (pdev i)) (TMuI (pdev IT) (pdev D))
          (pdev P)
          (TLam (TLam (TInd (lift 2 0 (pdev IT)) (lift 2 0 (pdev D))
            (lift 2 0 (pdev P)) (lift 2 0 (pdev st)) (TVar 1) (TVar 0))))
          (pdev xs))
  | TInd IT D P st i x =>
      TInd (pdev IT) (pdev D) (pdev P) (pdev st) (pdev i) (pdev x)
  | TIAll IT D X x P =>
      match D with
      | TIVar i => TApp (pdev P) (TPair (pdev i) (pdev x))
      | TI1 => match x with TUnit => TUnitT | _ => TIAll (pdev IT) (pdev D) (pdev X) (pdev x) (pdev P) end
      | TIBot => TUnitT
      | TIProd A B => match x with
          | TPair a b => TSigma (TIAll (pdev IT) (pdev A) (pdev X) (pdev a) (pdev P))
              (TIAll (lift 1 0 (pdev IT)) (lift 1 0 (pdev B)) (lift 1 0 (pdev X))
                (lift 1 0 (pdev b)) (lift 1 0 (pdev P)))
          | _ => TIAll (pdev IT) (pdev D) (pdev X) (pdev x) (pdev P) end
      | TIPi A T => TPi (pdev A)
          (TIAll (lift 1 0 (pdev IT)) (TApp (lift 1 0 (pdev T)) (TVar 0))
            (lift 1 0 (pdev X)) (TApp (lift 1 0 (pdev x)) (TVar 0)) (lift 1 0 (pdev P)))
      | TISig A T | TIChoice A T => match x with
          | TPair a b => TIAll (pdev IT) (TApp (pdev T) (pdev a)) (pdev X) (pdev b) (pdev P)
          | _ => TIAll (pdev IT) (pdev D) (pdev X) (pdev x) (pdev P) end
      | _ => TIAll (pdev IT) (pdev D) (pdev X) (pdev x) (pdev P)
      end
  | THyps IT D X P h x =>
      match D with
      | TIVar i => TApp (TApp (pdev h) (pdev i)) (pdev x)
      | TI1 => match x with TUnit => TUnit | _ => THyps (pdev IT) (pdev D) (pdev X) (pdev P) (pdev h) (pdev x) end
      | TIBot => TUnit
      | TIProd A B => match x with
          | TPair a b => TPair (THyps (pdev IT) (pdev A) (pdev X) (pdev P) (pdev h) (pdev a))
              (THyps (pdev IT) (pdev B) (pdev X) (pdev P) (pdev h) (pdev b))
          | _ => THyps (pdev IT) (pdev D) (pdev X) (pdev P) (pdev h) (pdev x) end
      | TIPi A T => TLam
          (THyps (lift 1 0 (pdev IT)) (TApp (lift 1 0 (pdev T)) (TVar 0))
            (lift 1 0 (pdev X)) (lift 1 0 (pdev P)) (lift 1 0 (pdev h))
            (TApp (lift 1 0 (pdev x)) (TVar 0)))
      | TISig A T | TIChoice A T => match x with
          | TPair a b => THyps (pdev IT) (TApp (pdev T) (pdev a)) (pdev X) (pdev P) (pdev h) (pdev b)
          | _ => THyps (pdev IT) (pdev D) (pdev X) (pdev P) (pdev h) (pdev x) end
      | _ => THyps (pdev IT) (pdev D) (pdev X) (pdev P) (pdev h) (pdev x)
      end
  | TClose IT F G => TClose (pdev IT) (pdev F) (pdev G)
  | TCloseCase k IT F G i Q b (TIn xs) => TApp (pdev b) (pdev xs)
  | TCloseCase k IT F G i Q b x =>
      TCloseCase k (pdev IT) (pdev F) (pdev G) (pdev i) (pdev Q) (pdev b) (pdev x)
  | TCloseInd IT G P st F i (TIn xs) =>
      TApp (TApp (TApp (TApp (pdev st) (pdev F)) (pdev i)) (pdev xs))
        (THyps (pdev IT) (TApp (pdev F) (pdev i))
          (TClose (pdev IT) (pdev G) (pdev G))
          (TLam (TApp (TApp (TApp (lift 1 0 (pdev P)) (lift 1 0 (pdev G)))
            (TFst (TVar 0))) (TSnd (TVar 0))))
          (TLam (TLam (TCloseInd (lift 2 0 (pdev IT)) (lift 2 0 (pdev G))
            (lift 2 0 (pdev P)) (lift 2 0 (pdev st)) (lift 2 0 (pdev G))
            (TVar 1) (TVar 0))))
          (pdev xs))
  | TCloseInd IT G P st F i x =>
      TCloseInd (pdev IT) (pdev G) (pdev P) (pdev st) (pdev F) (pdev i) (pdev x)
  end.

(* Invert parallel steps out of a known constructor shape. *)
Ltac inv_known :=
  match goal with
  | H : pstep (TLam _) _ |- _ => inversion H; subst; clear H
  | H : pstep (TPair _ _) _ |- _ => inversion H; subst; clear H
  | H : pstep TNilE _ |- _ => inversion H; subst; clear H
  | H : pstep (TConsE _ _) _ |- _ => inversion H; subst; clear H
  | H : pstep TEZero _ |- _ => inversion H; subst; clear H
  | H : pstep (TESucc _) _ |- _ => inversion H; subst; clear H
  | H : pstep TUnit _ |- _ => inversion H; subst; clear H
  | H : pstep (TIVar _) _ |- _ => inversion H; subst; clear H
  | H : pstep TI1 _ |- _ => inversion H; subst; clear H
  | H : pstep TIBot _ |- _ => inversion H; subst; clear H
  | H : pstep (TIProd _ _) _ |- _ => inversion H; subst; clear H
  | H : pstep (TIPi _ _) _ |- _ => inversion H; subst; clear H
  | H : pstep (TISig _ _) _ |- _ => inversion H; subst; clear H
  | H : pstep (TIChoice _ _) _ |- _ => inversion H; subst; clear H
  | H : pstep (TIn _) _ |- _ => inversion H; subst; clear H
  end.

(* Deterministic congruence closure for parallel steps. *)
Ltac ps_congr :=
  solve [ eassumption
        | apply pstep_refl
        | apply pstep_lift; ps_congr
        | apply pstep_subst; ps_congr
        | constructor; ps_congr ].

Ltac complete_finish :=
  cbn in *; repeat inv_known;
  solve [ ps_congr | apply_root ltac:(ps_congr) ].

