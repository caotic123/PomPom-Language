(* ========================================================================== *)
(* Progress for TypeRulesCore, with checked conversion and coverage metatheory.   *)
(* Weak-head separation, canonical-position uniqueness, and the enum          *)
(* contradiction and mu-application classification are proved below.         *)
(* Signature transport and progress are proved without global assumptions.   *)
(* The final Print Assumptions command audits the complete theorem.          *)
(* ========================================================================== *)

From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations.
Require Export TypeRulesCore.

(* ------------------------------------------------------------------ *)
(*  Term size, the induction measure                                   *)
(* ------------------------------------------------------------------ *)

Definition bsizeF (f : term -> nat) :=
  fix bsz (l : list (term * term)) : nat :=
    match l with
    | [] => 0
    | (c, b) :: l' => f c + f b + bsz l'
    end.

Fixpoint tsize (t : term) : nat :=
  match t with
  | TVar _ | TSort _ | TUnitT | TUnit | TUId | TTag _ | TEnumU | TNilE
  | TEZero | TI1 => 1
  | TLam b => S (tsize b)
  | TESucc n => S (tsize n)
  | TEnumT E => S (tsize E)
  | TIDesc IT => S (tsize IT)
  | TIVar i => S (tsize i)
  | TMuI R => S (tsize R)
  | TMuS Sf => S (tsize Sf)
  | TIn x => S (tsize x)
  | TFst p | TSnd p => S (tsize p)
  | TList A | TLNil A => S (tsize A)
  | TPi a b | TApp a b | TSigma a b | TPair a b | TConsE a b | TEPi a b
  | TIProd a b | TIPi a b | TISig a b | TIChoice a b | TInterp a b =>
      S (tsize a + tsize b)
  | TLCons a b c => S (tsize a + tsize b + tsize c)
  | TSwitch a b c d => S (tsize a + tsize b + tsize c + tsize d)
  | TIAll a b c d => S (tsize a + tsize b + tsize c + tsize d)
  | THyps a b c d e => S (tsize a + tsize b + tsize c + tsize d + tsize e)
  | TInd a b c d e => S (tsize a + tsize b + tsize c + tsize d + tsize e)
  | TCase M Q bs => S (tsize M + tsize Q + bsizeF tsize bs)
  end.

Notation bsize := (bsizeF tsize).

Lemma tsize_pos : forall t, 1 <= tsize t.
Proof. destruct t; cbn; lia. Qed.

Lemma tsize_strong_ind : forall (P : term -> Prop),
    (forall t, (forall u, tsize u < tsize t -> P u) -> P t) ->
    forall t, P t.
Proof.
  intros P H t.
  refine (@well_founded_induction nat lt lt_wf
            (fun n => forall u, tsize u = n -> P u)
            (fun n IH => _) (tsize t) t eq_refl).
  intros u Hn. apply H. intros v Hv.
  assert (Hv' : tsize v < n) by lia.
  exact (IH (tsize v) Hv' v eq_refl).
Qed.

Lemma bsize_in : forall bs c b, In (c, b) bs -> tsize c + tsize b <= bsize bs.
Proof.
  induction bs as [|[c0 b0] bs IH]; cbn; intros c b Hin.
  - destruct Hin.
  - destruct Hin as [Hin | Hin].
    + inversion Hin; subst; lia.
    + specialize (IH _ _ Hin); lia.
Qed.

Lemma tsize_case_bs : forall M Q bs c b,
    In (c, b) bs -> tsize c < tsize (TCase M Q bs).
Proof.
  intros M Q bs c b Hin.
  pose proof (bsize_in bs c b Hin) as H.
  pose proof (tsize_pos b) as Hb.
  change (tsize (TCase M Q bs)) with (S (tsize M + tsize Q + bsize bs)).
  lia.
Qed.

Lemma tsize_case_bs_body : forall M Q bs c b,
    In (c, b) bs -> tsize b < tsize (TCase M Q bs).
Proof.
  intros M Q bs c b Hin.
  pose proof (bsize_in bs c b Hin) as H.
  pose proof (tsize_pos c) as Hc.
  change (tsize (TCase M Q bs))
    with (S (tsize M + tsize Q + bsize bs)).
  lia.
Qed.

Lemma tsize_lift : forall t d k, tsize (lift d k t) = tsize t.
Proof.
  assert (Hmap : forall bs d k,
      (forall c b, In (c,b) bs ->
        tsize (lift d k c) = tsize c /\
        tsize (lift d (S k) b) = tsize b) ->
      bsize (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs) =
      bsize bs).
  {
    intros bs d k H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    rewrite (proj1 (H c b (or_introl eq_refl))).
    rewrite (proj2 (H c b (or_introl eq_refl))).
    rewrite (IH ltac:(intros c' b' Hin; apply H; right; exact Hin)).
    reflexivity.
  }
  apply (tsize_strong_ind (fun t => forall d k,
    tsize (lift d k t) = tsize t)).
  intros t IH d k. destruct t; cbn [lift tsize].
  all: try solve [destruct (Nat.ltb n k); reflexivity].
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5));
       cbn; lia);
    reflexivity].
  rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) d k).
  rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) d k).
  assert (HB :
      bsize (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs) =
      bsize bs).
  {
    apply Hmap; intros c b Hin; split.
    - apply IH; eapply tsize_case_bs; exact Hin.
    - apply IH; eapply tsize_case_bs_body; exact Hin.
  }
  rewrite HB. reflexivity.
Qed.

Lemma subst_lift_var : forall n k u,
    subst u k (lift 1 k (TVar n)) = TVar n.
Proof.
  intros n k u.
  cbn [lift].
  destruct (Nat.ltb n k) eqn:Hnk.
  - cbn [subst]. rewrite Hnk. reflexivity.
  - apply Nat.ltb_ge in Hnk.
    cbn [subst].
    destruct (Nat.ltb (1 + n) k) eqn:Hlift.
    + apply Nat.ltb_lt in Hlift. lia.
    + destruct (Nat.eqb (1 + n) k) eqn:Heq.
      * exfalso.
        pose proof (proj1 (Nat.eqb_eq (1 + n) k) Heq) as H.
        lia.
      * f_equal.
Qed.

Lemma subst_lift_cancel_size :
    forall n t, tsize t <= n ->
    forall u k, subst u k (lift 1 k t) = t.
Proof.
  induction n as [n IH] using lt_wf_ind.
  intros t Hsz u k.
  destruct t; cbn [lift subst]; cbn [tsize] in Hsz;
    try reflexivity; try apply subst_lift_var;
    repeat f_equal.

  all: try (eapply (IH (n - 1)); [lia | lia]).
  all: try lia.

  assert (Hbound :
    forall c b, In (c, b) bs ->
      tsize c < n /\ tsize b < n).
  {
    intros c b Hin.
    pose proof (bsize_in bs c b Hin) as Hb.
    pose proof (tsize_pos b) as Hbp.
    pose proof (tsize_pos c) as Hcp.
    cbn in Hsz.
    split; lia.
  }
  clear Hsz.

  induction bs as [| [c b] bs IHbs]; cbn.
  - reflexivity.
  - rewrite IHbs.
    + assert (Hcb := Hbound c b (or_introl eq_refl)).
      destruct Hcb as [Hc Hb].
      f_equal. f_equal.
      * eapply (IH (n - 1)); [lia | lia].
      * eapply (IH (n - 1)); [lia | lia].
    + intros c0 b0 Hin.
      apply Hbound. right; exact Hin.
  all: try lia.
Qed.

Lemma subst_lift_cancel :
    forall t u k, subst u k (lift 1 k t) = t.
Proof.
  intros t u k.
  apply (subst_lift_cancel_size (tsize t) t); lia.
Qed.

Lemma subst_lift_zero :
    forall f a, subst a 0 (lift 1 0 f) = f.
Proof. intros f a. apply subst_lift_cancel. Qed.

Lemma lift_lift_comm_var : forall n d e i j, i <= j ->
    lift d (e+j) (lift e i (TVar n)) = lift e i (lift d j (TVar n)).
Proof.
  intros n d e i j Hij.
  change (
    (lift d (e+j) (if Nat.ltb n i then TVar n else TVar (e+n))) =
    (lift e i (if Nat.ltb n j then TVar n else TVar (d+n)))).
  destruct (Nat.ltb n i) eqn:Hni;
    destruct (Nat.ltb n j) eqn:Hnj.
  - change (
      (if Nat.ltb n (e+j) then TVar n else TVar (d+n)) =
      (if Nat.ltb n i then TVar n else TVar (e+n))).
    apply Nat.ltb_lt in Hni. apply Nat.ltb_lt in Hnj.
    assert (Hout : Nat.ltb n (e+j) = true) by
      (apply Nat.ltb_lt; lia).
    rewrite Hout. rewrite <- Nat.ltb_lt in Hni. rewrite Hni. reflexivity.
  - apply Nat.ltb_lt in Hni. apply Nat.ltb_ge in Hnj. lia.
  - change (
      (if Nat.ltb (e+n) (e+j) then TVar (e+n) else TVar (d+(e+n))) =
      (if Nat.ltb n i then TVar n else TVar (e+n))).
    apply Nat.ltb_ge in Hni. apply Nat.ltb_lt in Hnj.
    assert (Hout : Nat.ltb (e+n) (e+j) = true) by
      (apply Nat.ltb_lt; lia).
    rewrite Hout. rewrite <- Nat.ltb_ge in Hni. rewrite Hni. reflexivity.
  - change (
      (if Nat.ltb (e+n) (e+j) then TVar (e+n) else TVar (d+(e+n))) =
      (if Nat.ltb (d+n) i then TVar (d+n) else TVar (e+(d+n)))).
    apply Nat.ltb_ge in Hni. apply Nat.ltb_ge in Hnj.
    assert (Hout : Nat.ltb (e+n) (e+j) = false) by
      (apply Nat.ltb_ge; lia).
    assert (Hin : Nat.ltb (d+n) i = false) by
      (apply Nat.ltb_ge; lia).
    rewrite Hout, Hin. f_equal. lia.
Qed.

Lemma lift_lift_comm : forall t d e i j, i <= j ->
    lift d (e + j) (lift e i t) = lift e i (lift d j t).
Proof.
  assert (Hmap : forall bs d e i j, i <= j ->
      (forall c b, In (c,b) bs ->
        lift d (e+j) (lift e i c) = lift e i (lift d j c) /\
        lift d (e+S j) (lift e (S i) b) =
          lift e (S i) (lift d (S j) b)) ->
      map (fun '(c,b) => (lift d (e+j) c, lift d (e+S j) b))
        (map (fun '(c,b) => (lift e i c, lift e (S i) b)) bs) =
      map (fun '(c,b) => (lift e i c, lift e (S i) b))
        (map (fun '(c,b) => (lift d j c, lift d (S j) b)) bs)).
  {
    intros bs d e i j Hij H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - replace (S (e+j)) with (e+S j) by lia.
      exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall d e i j, i <= j ->
    lift d (e+j) (lift e i t) = lift e i (lift d j t))).
  intros t IH d e i j Hij. destruct t.
  all: try solve [apply lift_lift_comm_var; exact Hij].
  all: cbn.
  all: try (replace (S (e+j)) with (e+S j) by lia).
  all: try reflexivity.
  all: try solve [repeat (erewrite IH by (cbn; lia)); reflexivity].
  all: repeat (erewrite IH by (cbn; lia)).
  all: f_equal.
  all: apply Hmap; [lia |].
  intros c b Hin. split.
  - apply IH; [eapply tsize_case_bs; exact Hin | lia].
  - apply IH; [eapply tsize_case_bs_body; exact Hin | lia].
Qed.

Corollary lift_lift_zero_comm : forall t d e k,
    lift d (e+k) (lift e 0 t) = lift e 0 (lift d k t).
Proof. intros; apply lift_lift_comm; lia. Qed.

Corollary lift_lift_one_zero : forall t d k,
    lift d (S k) (lift 1 0 t) = lift 1 0 (lift d k t).
Proof.
  intros t d k. replace (S k) with (1+k) by lia.
  apply lift_lift_comm; lia.
Qed.

Corollary lift_lift_one_one : forall t d k,
    lift d (S (S k)) (lift 1 1 t) = lift 1 1 (lift d (S k) t).
Proof.
  intros t d k. replace (S (S k)) with (1+S k) by lia.
  apply lift_lift_comm; lia.
Qed.

Corollary lift_lift_two_zero : forall t d k,
    lift d (S (S k)) (lift 2 0 t) = lift 2 0 (lift d k t).
Proof.
  intros t d k. replace (S (S k)) with (2+k) by lia.
  apply lift_lift_comm; lia.
Qed.

Lemma lift_fuse_var : forall n d e q i, i <= e ->
    lift d (q+i) (lift e q (TVar n)) = lift (d+e) q (TVar n).
Proof.
  intros n d e q i Hie.
  change ((lift d (q+i)
       (if Nat.ltb n q then TVar n else TVar (e+n))) =
    (if Nat.ltb n q then TVar n else TVar (d+e+n))).
  destruct (Nat.ltb n q) eqn:Hnq.
  - apply Nat.ltb_lt in Hnq.
    assert (Hout : Nat.ltb n (q+i) = true)
      by (apply Nat.ltb_lt; lia).
    cbn [lift]. rewrite Hout. reflexivity.
  - apply Nat.ltb_ge in Hnq.
    assert (Hout : Nat.ltb (e+n) (q+i) = false)
      by (apply Nat.ltb_ge; lia).
    cbn [lift]. rewrite Hout. f_equal. lia.
Qed.

Lemma lift_fuse : forall t d e q i, i <= e ->
    lift d (q+i) (lift e q t) = lift (d+e) q t.
Proof.
  assert (Hmap : forall bs d e q i, i <= e ->
      (forall c b, In (c,b) bs ->
        lift d (q+i) (lift e q c) = lift (d+e) q c /\
        lift d (S q+i) (lift e (S q) b) = lift (d+e) (S q) b) ->
      map (fun '(c,b) => (lift d (q+i) c, lift d (S q+i) b))
        (map (fun '(c,b) => (lift e q c, lift e (S q) b)) bs) =
      map (fun '(c,b) => (lift (d+e) q c, lift (d+e) (S q) b)) bs).
  {
    intros bs d e q i Hie H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - replace (S (q+i)) with (S q+i) by lia.
      exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right. exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall d e q i, i <= e ->
    lift d (q+i) (lift e q t) = lift (d+e) q t)).
  intros t IH d e q i Hie. destruct t.
  all: try solve [apply lift_fuse_var; exact Hie].
  all: cbn.
  all: try (replace (S (q+i)) with (S q+i) by lia).
  all: try reflexivity.
  all: try solve [repeat (erewrite IH by (cbn; lia)); reflexivity].
  all: repeat (erewrite IH by (cbn; lia)).
  all: f_equal.
  all: apply Hmap; [exact Hie |].
  intros c b Hin. split.
  - apply IH; [eapply tsize_case_bs; exact Hin | exact Hie].
  - apply IH; [eapply tsize_case_bs_body; exact Hin | exact Hie].
Qed.

Corollary lift_fuse_zero : forall t d e i, i <= e ->
    lift d i (lift e 0 t) = lift (d+e) 0 t.
Proof.
  intros t d e i H. replace i with (0+i) by lia.
  apply lift_fuse. exact H.
Qed.

Lemma subst_lift_offset_var : forall n u e i j, i <= j ->
    subst u (e+j) (lift e i (TVar n)) =
    lift e i (subst u j (TVar n)).
Proof.
  intros n u e i j Hij.
  destruct (Nat.lt_trichotomy n i) as [Hni | [Hni | Hni]].
  - assert (Hli : Nat.ltb n i = true) by (apply Nat.ltb_lt; lia).
    assert (Hlj : Nat.ltb n j = true) by (apply Nat.ltb_lt; lia).
    assert (Hlo : Nat.ltb n (e+j) = true) by (apply Nat.ltb_lt; lia).
    change (
      (subst u (e+j) (if Nat.ltb n i then TVar n else TVar (e+n))) =
      (lift e i
        (if Nat.ltb n j then TVar n
         else if Nat.eqb n j then lift j 0 u else TVar (pred n)))).
    rewrite Hli, Hlj.
    cbn [subst lift]. rewrite Hlo, Hli. reflexivity.
  - subst n.
    destruct (Nat.eq_dec i j) as [-> | Hij'].
    + assert (Hli : Nat.ltb j j = false) by (apply Nat.ltb_ge; lia).
      assert (Hei : Nat.eqb j j = true) by (apply Nat.eqb_eq; reflexivity).
      assert (Hlo : Nat.ltb (e+j) (e+j) = false) by
        (apply Nat.ltb_ge; lia).
      assert (Heo : Nat.eqb (e+j) (e+j) = true) by
        (apply Nat.eqb_eq; reflexivity).
      change (
        (subst u (e+j) (if Nat.ltb j j then TVar j else TVar (e+j))) =
        (lift e j
          (if Nat.ltb j j then TVar j
           else if Nat.eqb j j then lift j 0 u else TVar (pred j)))).
      rewrite Hli, Hei.
      cbn [subst]. rewrite Hlo, Heo.
      symmetry. apply lift_fuse_zero. lia.
    + assert (Hijlt : i < j) by lia.
      assert (Hli : Nat.ltb i i = false) by (apply Nat.ltb_ge; lia).
      assert (Hlj : Nat.ltb i j = true) by (apply Nat.ltb_lt; lia).
      assert (Hlo : Nat.ltb (e+i) (e+j) = true) by
        (apply Nat.ltb_lt; lia).
      change (
        (subst u (e+j) (if Nat.ltb i i then TVar i else TVar (e+i))) =
        (lift e i
          (if Nat.ltb i j then TVar i
           else if Nat.eqb i j then lift j 0 u else TVar (pred i)))).
      rewrite Hli, Hlj.
      cbn [subst lift]. rewrite Hlo, Hli. reflexivity.
  - destruct (Nat.lt_trichotomy n j) as [Hnj | [Hnj | Hnj]].
    + assert (Hli : Nat.ltb n i = false) by (apply Nat.ltb_ge; lia).
      assert (Hlj : Nat.ltb n j = true) by (apply Nat.ltb_lt; lia).
      assert (Hlo : Nat.ltb (e+n) (e+j) = true) by
        (apply Nat.ltb_lt; lia).
      change (
        (subst u (e+j) (if Nat.ltb n i then TVar n else TVar (e+n))) =
        (lift e i
          (if Nat.ltb n j then TVar n
           else if Nat.eqb n j then lift j 0 u else TVar (pred n)))).
      rewrite Hli, Hlj.
      cbn [subst lift]. rewrite Hlo, Hli. reflexivity.
    + subst n.
      assert (Hli : Nat.ltb j i = false) by (apply Nat.ltb_ge; lia).
      assert (Hlj : Nat.ltb j j = false) by (apply Nat.ltb_ge; lia).
      assert (Hej : Nat.eqb j j = true) by (apply Nat.eqb_eq; reflexivity).
      assert (Hlo : Nat.ltb (e+j) (e+j) = false) by
        (apply Nat.ltb_ge; lia).
      assert (Heo : Nat.eqb (e+j) (e+j) = true) by
        (apply Nat.eqb_eq; reflexivity).
      change (
        (subst u (e+j) (if Nat.ltb j i then TVar j else TVar (e+j))) =
        (lift e i
          (if Nat.ltb j j then TVar j
           else if Nat.eqb j j then lift j 0 u else TVar (pred j)))).
      rewrite Hli, Hlj, Hej.
      cbn [subst]. rewrite Hlo, Heo.
      symmetry. apply lift_fuse_zero. lia.
    + assert (Hli : Nat.ltb n i = false) by (apply Nat.ltb_ge; lia).
      assert (Hlj : Nat.ltb n j = false) by (apply Nat.ltb_ge; lia).
      assert (Hej : Nat.eqb n j = false) by (apply Nat.eqb_neq; lia).
      assert (Hlo : Nat.ltb (e+n) (e+j) = false) by
        (apply Nat.ltb_ge; lia).
      assert (Heo : Nat.eqb (e+n) (e+j) = false) by
        (apply Nat.eqb_neq; lia).
      assert (Hpred : Nat.ltb (pred n) i = false) by
        (apply Nat.ltb_ge; destruct n; cbn in *; lia).
      change (
        (subst u (e+j) (if Nat.ltb n i then TVar n else TVar (e+n))) =
        (lift e i
          (if Nat.ltb n j then TVar n
           else if Nat.eqb n j then lift j 0 u else TVar (pred n)))).
      rewrite Hli, Hlj, Hej.
      cbn [subst lift]. rewrite Hlo, Heo, Hpred.
      f_equal. destruct n; cbn in *; lia.
Qed.

Lemma subst_lift_offset : forall t u e i j, i <= j ->
    subst u (e+j) (lift e i t) = lift e i (subst u j t).
Proof.
  assert (Hmap : forall bs u e i j, i <= j ->
      (forall c b, In (c,b) bs ->
        subst u (e+j) (lift e i c) = lift e i (subst u j c) /\
        subst u (e+S j) (lift e (S i) b) =
          lift e (S i) (subst u (S j) b)) ->
      map (fun '(c,b) => (subst u (e+j) c, subst u (e+S j) b))
        (map (fun '(c,b) => (lift e i c, lift e (S i) b)) bs) =
      map (fun '(c,b) => (lift e i c, lift e (S i) b))
        (map (fun '(c,b) => (subst u j c, subst u (S j) b)) bs)).
  {
    intros bs u e i j Hij H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - replace (S (e+j)) with (e+S j) by lia.
      exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right. exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall u e i j, i <= j ->
    subst u (e+j) (lift e i t) = lift e i (subst u j t))).
  intros t IH u e i j Hij. destruct t.
  all: try solve [apply subst_lift_offset_var; exact Hij].
  all: cbn.
  all: try (replace (S (e+j)) with (e+S j) by lia).
  all: try reflexivity.
  all: try solve [repeat (erewrite IH by (cbn; lia)); reflexivity].
  all: repeat (erewrite IH by (cbn; lia)).
  all: f_equal.
  all: apply Hmap; [exact Hij |].
  intros c b Hin. split.
  - apply IH; [eapply tsize_case_bs; exact Hin | exact Hij].
  - apply IH; [eapply tsize_case_bs_body; exact Hin | lia].
Qed.

Corollary subst_lift_one_zero : forall t u k,
    subst u (S k) (lift 1 0 t) = lift 1 0 (subst u k t).
Proof.
  intros t u k. replace (S k) with (1+k) by lia.
  apply subst_lift_offset. lia.
Qed.

Corollary subst_lift_one_one : forall t u k,
    subst u (S (S k)) (lift 1 1 t) = lift 1 1 (subst u (S k) t).
Proof.
  intros t u k. replace (S (S k)) with (1+S k) by lia.
  apply subst_lift_offset. lia.
Qed.

Corollary subst_lift_two_zero : forall t u k,
    subst u (S (S k)) (lift 2 0 t) = lift 2 0 (subst u k t).
Proof.
  intros t u k. replace (S (S k)) with (2+k) by lia.
  apply subst_lift_offset. lia.
Qed.

Lemma subst_subst_comm_var : forall n u a k j,
    subst u (j+k) (subst a j (TVar n)) =
    subst (subst u k a) j (subst u (j+S k) (TVar n)).
Proof.
  intros n u a k j.
  destruct (Nat.lt_trichotomy n j) as [Hnj | [Hnj | Hnj]].
  - assert (H1 : Nat.ltb n j = true) by (apply Nat.ltb_lt; lia).
    assert (H2 : Nat.ltb n (j+k) = true) by (apply Nat.ltb_lt; lia).
    assert (H3 : Nat.ltb n (j+S k) = true) by (apply Nat.ltb_lt; lia).
    change (
      subst u (j+k)
        (if Nat.ltb n j then TVar n
         else if Nat.eqb n j then lift j 0 a else TVar (pred n)) =
      subst (subst u k a) j
        (if Nat.ltb n (j+S k) then TVar n
         else if Nat.eqb n (j+S k) then lift (j+S k) 0 u
              else TVar (pred n))).
    rewrite H1, H3.
    cbn [subst]. rewrite H2, H1. reflexivity.
  - subst n.
    assert (H1 : Nat.ltb j j = false) by (apply Nat.ltb_ge; lia).
    assert (He : Nat.eqb j j = true) by (apply Nat.eqb_eq; reflexivity).
    assert (H3 : Nat.ltb j (j+S k) = true) by (apply Nat.ltb_lt; lia).
    change (
      subst u (j+k)
        (if Nat.ltb j j then TVar j
         else if Nat.eqb j j then lift j 0 a else TVar (pred j)) =
      subst (subst u k a) j
        (if Nat.ltb j (j+S k) then TVar j
         else if Nat.eqb j (j+S k) then lift (j+S k) 0 u
              else TVar (pred j))).
    rewrite H1, He, H3.
    rewrite (subst_lift_offset a u j 0 k) by lia.
    cbn [subst]. rewrite H1, He. reflexivity.
  - destruct n as [|q]; [lia |]. cbn [pred].
    destruct (Nat.lt_trichotomy q (j+k)) as [Hq | [Hq | Hq]].
    + assert (H1 : Nat.ltb (S q) j = false) by
        (apply Nat.ltb_ge; lia).
      assert (He : Nat.eqb (S q) j = false) by
        (apply Nat.eqb_neq; lia).
      assert (H2 : Nat.ltb q (j+k) = true) by (apply Nat.ltb_lt; lia).
      assert (H3 : Nat.ltb (S q) (j+S k) = true) by
        (apply Nat.ltb_lt; lia).
      change (
        subst u (j+k)
          (if Nat.ltb (S q) j then TVar (S q)
           else if Nat.eqb (S q) j then lift j 0 a else TVar q) =
        subst (subst u k a) j
          (if Nat.ltb (S q) (j+S k) then TVar (S q)
           else if Nat.eqb (S q) (j+S k) then lift (j+S k) 0 u
                else TVar q)).
      rewrite H1, He, H3.
      cbn [subst]. rewrite H2, H1, He. reflexivity.
    + subst q.
      assert (H1 : Nat.ltb (S (j+k)) j = false) by
        (apply Nat.ltb_ge; lia).
      assert (He : Nat.eqb (S (j+k)) j = false) by
        (apply Nat.eqb_neq; lia).
      assert (H2 : Nat.ltb (j+k) (j+k) = false) by
        (apply Nat.ltb_ge; lia).
      assert (He2 : Nat.eqb (j+k) (j+k) = true) by
        (apply Nat.eqb_eq; reflexivity).
      assert (H3 : Nat.ltb (S (j+k)) (j+S k) = false) by
        (apply Nat.ltb_ge; lia).
      assert (He3 : Nat.eqb (S (j+k)) (j+S k) = true) by
        (apply Nat.eqb_eq; lia).
      change (
        subst u (j+k)
          (if Nat.ltb (S (j+k)) j then TVar (S (j+k))
           else if Nat.eqb (S (j+k)) j then lift j 0 a else TVar (j+k)) =
        subst (subst u k a) j
          (if Nat.ltb (S (j+k)) (j+S k) then TVar (S (j+k))
           else if Nat.eqb (S (j+k)) (j+S k) then lift (j+S k) 0 u
                else TVar (j+k))).
      rewrite H1, He, H3, He3.
      cbn [subst]. rewrite H2, He2.
      replace (lift (j+S k) 0 u)
        with (lift 1 j (lift (j+k) 0 u)).
      * rewrite subst_lift_cancel. reflexivity.
      * rewrite lift_fuse_zero by lia. f_equal. lia.
    + assert (H1 : Nat.ltb (S q) j = false) by
        (apply Nat.ltb_ge; lia).
      assert (He : Nat.eqb (S q) j = false) by
        (apply Nat.eqb_neq; lia).
      assert (H2 : Nat.ltb q (j+k) = false) by
        (apply Nat.ltb_ge; lia).
      assert (He2 : Nat.eqb q (j+k) = false) by
        (apply Nat.eqb_neq; lia).
      assert (H3 : Nat.ltb (S q) (j+S k) = false) by
        (apply Nat.ltb_ge; lia).
      assert (He3 : Nat.eqb (S q) (j+S k) = false) by
        (apply Nat.eqb_neq; lia).
      assert (H4 : Nat.ltb q j = false) by (apply Nat.ltb_ge; lia).
      assert (He4 : Nat.eqb q j = false) by (apply Nat.eqb_neq; lia).
      change (
        subst u (j+k)
          (if Nat.ltb (S q) j then TVar (S q)
           else if Nat.eqb (S q) j then lift j 0 a else TVar q) =
        subst (subst u k a) j
          (if Nat.ltb (S q) (j+S k) then TVar (S q)
           else if Nat.eqb (S q) (j+S k) then lift (j+S k) 0 u
                else TVar q)).
      rewrite H1, He, H3, He3.
      cbn [subst]. rewrite H2, He2, H4, He4. reflexivity.
Qed.

Lemma subst_subst_comm : forall t u a k j,
    subst u (j+k) (subst a j t) =
    subst (subst u k a) j (subst u (j+S k) t).
Proof.
  assert (Hmap : forall bs u a k j,
      (forall c b, In (c,b) bs ->
        subst u (j+k) (subst a j c) =
          subst (subst u k a) j (subst u (j+S k) c) /\
        subst u (S j+k) (subst a (S j) b) =
          subst (subst u k a) (S j) (subst u (S j+S k) b)) ->
      map (fun '(c,b) => (subst u (j+k) c, subst u (S j+k) b))
        (map (fun '(c,b) => (subst a j c, subst a (S j) b)) bs) =
      map (fun '(c,b) =>
        (subst (subst u k a) j c, subst (subst u k a) (S j) b))
        (map (fun '(c,b) => (subst u (j+S k) c, subst u (S j+S k) b)) bs)).
  {
    intros bs u a k j H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right. exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall u a k j,
    subst u (j+k) (subst a j t) =
    subst (subst u k a) j (subst u (j+S k) t))).
  intros t IH u a k j. destruct t.
  all: try solve [apply subst_subst_comm_var].
  all: cbn.
  all: try reflexivity.
  all: try solve [f_equal; apply IH; cbn; lia].
  all: f_equal.
  all: try solve [apply IH; cbn; lia].
  all: try solve [
    replace (S (j+k)) with (S j+k) by lia;
    replace (S (j+S k)) with (S j+S k) by lia;
    apply IH; cbn; lia].
  all: apply Hmap.
  intros c b Hin. split.
  - apply IH. eapply tsize_case_bs; exact Hin.
  - apply IH. eapply tsize_case_bs_body; exact Hin.
Qed.

Corollary subst_subst_zero_comm : forall t u a k,
    subst u k (subst a 0 t) =
    subst (subst u k a) 0 (subst u (S k) t).
Proof.
  intros t u a k.
  replace k with (0+k) by lia.
  replace (S k) with (0+S k) by lia.
  apply subst_subst_comm.
Qed.

Lemma lift_subst_comm_var : forall n a d k j,
    lift d (k+j) (subst a j (TVar n)) =
    subst (lift d k a) j (lift d (S k+j) (TVar n)).
Proof.
  intros n a d k j.
  destruct (Nat.lt_trichotomy n j) as [Hlt | [Heq | Hgt]].
  - assert (H1 : Nat.ltb n j = true) by (apply Nat.ltb_lt; lia).
    assert (H2 : Nat.ltb n (k+j) = true) by (apply Nat.ltb_lt; lia).
    assert (H3 : Nat.ltb n (S k+j) = true) by (apply Nat.ltb_lt; lia).
    change ((lift d (k+j)
      (if Nat.ltb n j then TVar n
       else if Nat.eqb n j then lift j 0 a else TVar (pred n))) =
      (subst (lift d k a) j
        (if Nat.ltb n (S k+j) then TVar n else TVar (d+n)))).
    rewrite H1, H3.
    change ((if Nat.ltb n (k+j) then TVar n else TVar (d+n)) =
      (if Nat.ltb n j then TVar n
       else if Nat.eqb n j then lift j 0 (lift d k a) else TVar (pred n))).
    rewrite H1, H2. reflexivity.
  - subst n.
    assert (H1 : Nat.ltb j j = false) by (apply Nat.ltb_ge; lia).
    assert (He : Nat.eqb j j = true) by (apply Nat.eqb_eq; reflexivity).
    assert (H3 : Nat.ltb j (S k+j) = true) by (apply Nat.ltb_lt; lia).
    change ((lift d (k+j)
      (if Nat.ltb j j then TVar j
       else if Nat.eqb j j then lift j 0 a else TVar (pred j))) =
      (subst (lift d k a) j
        (if Nat.ltb j (S k+j) then TVar j else TVar (d+j)))).
    rewrite H1, He, H3.
    unfold subst; fold subst. rewrite H1, He.
    change (lift d (k+j) (lift j 0 a) = lift j 0 (lift d k a)).
    rewrite Nat.add_comm. apply lift_lift_comm; lia.
  - assert (H1 : Nat.ltb n j = false) by (apply Nat.ltb_ge; lia).
    assert (He : Nat.eqb n j = false) by
      (apply Nat.eqb_neq; lia).
    destruct n as [|q]; [lia |]. cbn [pred].
    destruct (Nat.ltb q (k+j)) eqn:Hq.
    + apply Nat.ltb_lt in Hq.
      assert (H3 : Nat.ltb (S q) (S k+j) = true) by
        (apply Nat.ltb_lt; lia).
      assert (Hj : Nat.ltb (S q) j = false) by
        (apply Nat.ltb_ge; lia).
      assert (Hej : Nat.eqb (S q) j = false) by
        (apply Nat.eqb_neq; lia).
      change ((lift d (k+j)
        (if Nat.ltb (S q) j then TVar (S q)
         else if Nat.eqb (S q) j then lift j 0 a else TVar q)) =
        (subst (lift d k a) j
          (if Nat.ltb (S q) (S k+j) then TVar (S q)
           else TVar (d+S q)))).
      rewrite H1, He, H3.
      change ((if Nat.ltb q (k+j) then TVar q else TVar (d+q)) =
        (if Nat.ltb (S q) j then TVar (S q)
         else if Nat.eqb (S q) j then lift j 0 (lift d k a) else TVar q)).
      rewrite Hj, Hej. rewrite <- Nat.ltb_lt in Hq. rewrite Hq. reflexivity.
    + apply Nat.ltb_ge in Hq.
      assert (H3 : Nat.ltb (S q) (S k+j) = false) by
        (apply Nat.ltb_ge; lia).
      assert (Hdj : Nat.ltb (d+S q) j = false) by
        (apply Nat.ltb_ge; lia).
      assert (Hedj : Nat.eqb (d+S q) j = false) by
        (apply Nat.eqb_neq; lia).
      change ((lift d (k+j)
        (if Nat.ltb (S q) j then TVar (S q)
         else if Nat.eqb (S q) j then lift j 0 a else TVar q)) =
        (subst (lift d k a) j
          (if Nat.ltb (S q) (S k+j) then TVar (S q)
           else TVar (d+S q)))).
      rewrite H1, He, H3.
      change ((if Nat.ltb q (k+j) then TVar q else TVar (d+q)) =
        (if Nat.ltb (d+S q) j then TVar (d+S q)
         else if Nat.eqb (d+S q) j then lift j 0 (lift d k a)
              else TVar (pred (d+S q)))).
      rewrite Hdj, Hedj. rewrite <- Nat.ltb_ge in Hq. rewrite Hq.
      f_equal. destruct d; cbn; lia.
Qed.

Lemma lift_subst_comm : forall t a d k j,
    lift d (j+k) (subst a j t) =
    subst (lift d k a) j (lift d (j+S k) t).
Proof.
  assert (Hmap : forall bs a d k j,
      (forall c b, In (c,b) bs ->
        lift d (j+k) (subst a j c) =
          subst (lift d k a) j (lift d (j+S k) c) /\
        lift d (S j+k) (subst a (S j) b) =
          subst (lift d k a) (S j) (lift d (S j+S k) b)) ->
      map (fun '(c,b) => (lift d (j+k) c, lift d (S j+k) b))
        (map (fun '(c,b) => (subst a j c, subst a (S j) b)) bs) =
      map (fun '(c,b) =>
        (subst (lift d k a) j c, subst (lift d k a) (S j) b))
        (map (fun '(c,b) => (lift d (j+S k) c, lift d (S j+S k) b)) bs)).
  {
    intros bs a d k j H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall a d k j,
    lift d (j+k) (subst a j t) =
    subst (lift d k a) j (lift d (j+S k) t))).
  intros t IH a d k j. destruct t.
  all: try solve [rewrite Nat.add_comm;
    replace (j + S k) with (S k + j) by lia;
    apply lift_subst_comm_var].
  all: cbn.
  all: try reflexivity.
  all: try solve [f_equal; apply IH; cbn; lia].
  all: f_equal.
  all: try solve [apply IH; cbn; lia].
  all: try solve [
    replace (S (j+k)) with (S j+k) by lia;
    replace (S (j+S k)) with (S j+S k) by lia;
    apply IH; cbn; lia].
  all: apply Hmap.
  intros c b Hin. split.
  - apply IH. eapply tsize_case_bs; exact Hin.
  - apply IH. eapply tsize_case_bs_body; exact Hin.
Qed.

Corollary lift_subst_zero_comm : forall t a d k,
    lift d k (subst a 0 t) =
    subst (lift d k a) 0 (lift d (S k) t).
Proof.
  intros t a d k.
  replace k with (0+k) by lia.
  replace (S k) with (0+S k) by lia.
  apply lift_subst_comm.
Qed.

(* Erase the signature body carried by [TMuS].  Phi conversion only equates
   applications of that opaque former; after erasure every such equation is
   literal reflexivity, while all other syntax remains visible. *)
Fixpoint phi_erase (t : term) : term :=
  match t with
  | TVar n => TVar n | TSort k => TSort k
  | TPi A B => TPi (phi_erase A) (phi_erase B)
  | TLam b => TLam (phi_erase b)
  | TApp f a => TApp (phi_erase f) (phi_erase a)
  | TSigma A B => TSigma (phi_erase A) (phi_erase B)
  | TPair a b => TPair (phi_erase a) (phi_erase b)
  | TFst p => TFst (phi_erase p) | TSnd p => TSnd (phi_erase p)
  | TUnitT => TUnitT | TUnit => TUnit | TUId => TUId | TTag s => TTag s
  | TEnumU => TEnumU | TNilE => TNilE
  | TConsE t E => TConsE (phi_erase t) (phi_erase E)
  | TEnumT E => TEnumT (phi_erase E)
  | TEZero => TEZero | TESucc n => TESucc (phi_erase n)
  | TEPi E P => TEPi (phi_erase E) (phi_erase P)
  | TSwitch E P p e =>
      TSwitch (phi_erase E) (phi_erase P) (phi_erase p) (phi_erase e)
  | TIDesc IT => TIDesc (phi_erase IT) | TIVar i => TIVar (phi_erase i)
  | TI1 => TI1
  | TIProd A B => TIProd (phi_erase A) (phi_erase B)
  | TIPi Sd T => TIPi (phi_erase Sd) (phi_erase T)
  | TISig Sd T => TISig (phi_erase Sd) (phi_erase T)
  | TIChoice E T => TIChoice (phi_erase E) (phi_erase T)
  | TInterp D X => TInterp (phi_erase D) (phi_erase X)
  | TMuI R => TMuI (phi_erase R)
  | TMuS _ => TMuS TUnit
  | TIn x => TIn (phi_erase x)
  | TInd R P stp i x =>
      TInd (phi_erase R) (phi_erase P) (phi_erase stp)
           (phi_erase i) (phi_erase x)
  | TIAll D X xs P =>
      TIAll (phi_erase D) (phi_erase X) (phi_erase xs) (phi_erase P)
  | THyps D X P h xs =>
      THyps (phi_erase D) (phi_erase X) (phi_erase P)
            (phi_erase h) (phi_erase xs)
  | TList A => TList (phi_erase A)
  | TLNil A => TLNil (phi_erase A)
  | TLCons A a l => TLCons (phi_erase A) (phi_erase a) (phi_erase l)
  | TCase M Q bs =>
      TCase (phi_erase M) (phi_erase Q)
        (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs)
  end.

Lemma phi_erase_lift : forall t d k,
    phi_erase (lift d k t) = lift d k (phi_erase t).
Proof.
  assert (Hmap : forall bs d k,
      (forall c b, In (c,b) bs ->
       phi_erase (lift d k c) = lift d k (phi_erase c) /\
       phi_erase (lift d (S k) b) = lift d (S k) (phi_erase b)) ->
      map (fun '(c,b) => (phi_erase c, phi_erase b))
          (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs) =
      map (fun '(c,b) => (lift d k c, lift d (S k) b))
          (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs)).
  {
    intros bs d k H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity|].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall d k,
    phi_erase (lift d k t) = lift d k (phi_erase t))).
  intros t IH d k. destruct t; cbn.
  all: try solve [destruct k as [|k]; cbn; [reflexivity |];
                  destruct (Nat.leb n k); reflexivity].
  all: try solve [repeat f_equal; try reflexivity;
    try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia)].
  all: try (apply f_equal3).
  all: try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia).
  all: apply Hmap; intros c b Hin; split;
    [ apply IH; eapply tsize_case_bs; exact Hin
    | apply IH; eapply tsize_case_bs_body; exact Hin ].
Qed.

Lemma phi_erase_subst : forall t u k,
    phi_erase (subst u k t) = subst (phi_erase u) k (phi_erase t).
Proof.
  assert (Hmap : forall bs u k,
      (forall c b, In (c,b) bs ->
       phi_erase (subst u k c) = subst (phi_erase u) k (phi_erase c) /\
       phi_erase (subst u (S k) b) =
         subst (phi_erase u) (S k) (phi_erase b)) ->
      map (fun '(c,b) => (phi_erase c, phi_erase b))
          (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs) =
      map (fun '(c,b) =>
             (subst (phi_erase u) k c,
              subst (phi_erase u) (S k) b))
          (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs)).
  {
    intros bs u k H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity|].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall u k,
    phi_erase (subst u k t) = subst (phi_erase u) k (phi_erase t))).
  intros t IH u k. destruct t; cbn.
  all: try solve [destruct k as [|k]; cbn;
    [ destruct n; cbn; try reflexivity;
      rewrite phi_erase_lift; reflexivity
    | destruct (Nat.leb n k); cbn; try reflexivity;
      destruct (Nat.eqb n (S k)); cbn; try reflexivity;
      rewrite phi_erase_lift; reflexivity ]].
  all: try (f_equal; try reflexivity;
    try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia)).
  all: try (apply f_equal3).
  all: try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia).
  all: apply Hmap; intros c b Hin; split;
    [ apply IH; eapply tsize_case_bs; exact Hin
    | apply IH; eapply tsize_case_bs_body; exact Hin ].
Qed.

Lemma phi_erase_enum_pos : forall c n, enum_pos c n ->
    enum_pos (phi_erase c) n.
Proof. intros c n H. induction H; cbn; constructor; assumption. Qed.

Lemma phi_erase_nth_error : forall bs k c b,
    nth_error bs k = Some (c,b) ->
    nth_error (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs) k =
      Some (phi_erase c, phi_erase b).
Proof.
  intros bs k. revert k.
  induction bs as [|[c0 b0] bs IH]; intros [|k] c b H;
    cbn in *; try discriminate.
  - inversion H; reflexivity.
  - apply IH; exact H.
Qed.

Lemma phi_erase_nth_inv : forall bs k c b,
    nth_error (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs) k =
      Some (c,b) ->
    exists c0 b0, nth_error bs k = Some (c0,b0) /\
      phi_erase c0 = c /\ phi_erase b0 = b.
Proof.
  intros bs k. revert k.
  induction bs as [|[c0 b0] bs IH];
    intros [|k] c b H; cbn in *; try discriminate.
  - inversion H; subst. eexists; eexists; repeat split; reflexivity.
  - destruct (IH k c b H) as [c1 [b1 [H1 [H2 H3]]]].
    exists c1, b1. repeat split; cbn; assumption.
Qed.

Lemma phi_erase_step : forall t u,
    step t u -> step (phi_erase t) (phi_erase u).
Proof.
  intros t u H; induction H.
  all: cbn; try constructor; eauto.
  - rewrite phi_erase_subst. apply st_beta.
  - repeat rewrite phi_erase_lift. apply st_epi_cons.
  - repeat rewrite phi_erase_lift. apply st_switch_succ.
  - repeat rewrite phi_erase_lift. apply st_interp_prod.
  - repeat rewrite phi_erase_lift. apply st_interp_pi.
  - repeat rewrite phi_erase_lift. apply st_interp_sig.
  - repeat rewrite phi_erase_lift. apply st_interp_choice.
  - repeat rewrite phi_erase_lift. apply st_iall_prod.
  - repeat rewrite phi_erase_lift. apply st_iall_pi.
  - repeat rewrite phi_erase_lift. apply st_hyps_pi.
  - repeat rewrite phi_erase_lift. apply st_ind.
  - rewrite phi_erase_subst.
    apply st_case with
      (a := phi_erase a) (xs := phi_erase xs) (Q := phi_erase Q)
      (bs := map (fun '(c,b) => (phi_erase c, phi_erase b)) bs)
      (k := k) (c := phi_erase c) (b := phi_erase b) (n := n).
    + apply phi_erase_nth_error. exact H.
    + apply phi_erase_enum_pos. exact H0.
    + apply phi_erase_enum_pos. exact H1.
    + intros j cj bj Hj Hnth.
      destruct (phi_erase_nth_inv _ _ _ _ Hnth)
        as [cj0 [bj0 [Hsrc [Hc Hb]]]].
      destruct (H2 j cj0 bj0 Hj Hsrc) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite <- Hc. apply phi_erase_enum_pos. exact Hpos.
      * exact Hneq.
  - repeat rewrite map_app. cbn.
    apply st_case_lbl. exact IHstep.
Qed.

(* ------------------------------------------------------------------ *)
(*  Small helpers                                                      *)
(* ------------------------------------------------------------------ *)

Lemma eval_trans : forall a b c, eval a b -> eval b c -> eval a c.
Proof.
  intros a b c H; revert c; induction H; intros; eauto.
  eapply ev_step; eauto.
Qed.

Lemma conv_of_eval : forall t u, eval t u -> conv t u.
Proof.
  intros t u H; induction H.
  - apply cv_refl.
  - eapply cv_trans; [apply cv_step; exact H | exact IHeval].
Qed.

Lemma conv_of_common_eval : forall t u v,
    eval t u -> eval t v -> conv u v.
Proof.
  intros t u v Hu Hv. eapply cv_trans.
  - apply cv_sym, conv_of_eval, Hu.
  - apply conv_of_eval, Hv.
Qed.

Lemma conv_eval_right : forall t u v,
    eval t u -> conv u v -> conv t v.
Proof.
  intros t u v He Hc. eapply cv_trans; [apply conv_of_eval, He | exact Hc].
Qed.

(* A small, local closure library for the conversion metatheory below. *)
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

Lemma check_of_synth : forall G t A, synth G t A -> check G t A.
Proof. intros; eapply ch_conv; [eassumption | apply cv_refl]. Qed.

(* canonical positions are step-normal (also proved in the smoke suite;
   needed here for the eval-invariance of a canonical scrutinee tag) *)
Lemma pos_step_normal : forall c n, enum_pos c n -> forall c', ~ step c c'.
Proof.
  intros c n H. induction H; intros c' Hs.
  - inversion Hs.
  - inversion Hs; subst. eapply IHenum_pos; eauto.
Qed.

Lemma enum_pos_functional : forall c n m,
    enum_pos c n -> enum_pos c m -> n = m.
Proof.
  intros c n m Hn. revert m. induction Hn; intros m Hm.
  - inversion Hm. reflexivity.
  - inversion Hm; subst. f_equal. eapply IHHn. assumption.
Qed.

Lemma enum_pos_injective : forall c d n,
    enum_pos c n -> enum_pos d n -> c = d.
Proof.
  intros c d n Hc. revert d. induction Hc; intros d Hd.
  - inversion Hd. reflexivity.
  - inversion Hd; subst. f_equal. eapply IHHc. assumption.
Qed.

Lemma enum_pos_lift_id : forall c n, enum_pos c n ->
    forall d k, lift d k c = c.
Proof.
  intros c n H. induction H; intros d k; cbn; [reflexivity |].
  f_equal. apply IHenum_pos.
Qed.

Lemma enum_pos_subst_id : forall c n, enum_pos c n ->
    forall u k, subst u k c = c.
Proof.
  intros c n H. induction H; intros u k; cbn; [reflexivity |].
  f_equal. apply IHenum_pos.
Qed.

Lemma nth_error_lift_branches : forall bs k c b d q,
    nth_error bs k = Some (c,b) ->
    nth_error
      (map (fun '(c,b) => (lift d q c, lift d (S q) b)) bs) k =
    Some (lift d q c, lift d (S q) b).
Proof.
  induction bs as [|[c0 b0] bs IH]; intros k c b d q H.
  - destruct k; cbn in H; discriminate.
  - destruct k as [|k].
    + cbn in H |- *. inversion H. reflexivity.
    + cbn in H |- *. eapply IH. exact H.
Qed.

Lemma nth_error_subst_branches : forall bs k c b u q,
    nth_error bs k = Some (c,b) ->
    nth_error
      (map (fun '(c,b) => (subst u q c, subst u (S q) b)) bs) k =
    Some (subst u q c, subst u (S q) b).
Proof.
  induction bs as [|[c0 b0] bs IH]; intros k c b u q H.
  - destruct k; cbn in H; discriminate.
  - destruct k as [|k].
    + cbn in H |- *. inversion H. reflexivity.
    + cbn in H |- *. eapply IH. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(*  Weak-head classification                                           *)
(* ------------------------------------------------------------------ *)

Inductive htag : Type :=
| HSort | HPi | HSigma | HUnitT | HUId | HEnumU | HEnumT | HIDesc | HList
| HMuIApp | HMuSApp | HNilE | HConsE.

(* Top-level shapes.  All classified shapes are completely step-normal:
   none has a head rule, and none has an argument congruence (TApp with a
   μ head included — st_app1 needs the function to step and μ formers do
   not).  λ is deliberately UNclassified: eta makes it head-promiscuous. *)
Inductive hshape : term -> htag -> Prop :=
| hs_sort   : forall k, hshape (TSort k) HSort
| hs_pi     : forall A B, hshape (TPi A B) HPi
| hs_sigma  : forall A B, hshape (TSigma A B) HSigma
| hs_unitT  : hshape TUnitT HUnitT
| hs_uid    : hshape TUId HUId
| hs_enumu  : hshape TEnumU HEnumU
| hs_enumt  : forall E, hshape (TEnumT E) HEnumT
| hs_idesc  : forall IT, hshape (TIDesc IT) HIDesc
| hs_list   : forall A, hshape (TList A) HList
| hs_muiapp : forall R i, hshape (TApp (TMuI R) i) HMuIApp
| hs_musapp : forall Sf i, hshape (TApp (TMuS Sf) i) HMuSApp
| hs_nile   : hshape TNilE HNilE
| hs_conse  : forall tg E, hshape (TConsE tg E) HConsE.

Definition whd (T : term) (h : htag) : Prop :=
  exists T', eval T T' /\ hshape T' h.

Lemma whd_shape : forall T h, hshape T h -> whd T h.
Proof. intros; exists T; split; [apply ev_refl | assumption]. Qed.

(* Rigid weak-head shapes have no weak-head successor.  Keeping this
   independent of conversion makes it reusable in the confluence
   corollaries below. *)
Lemma hshape_step_normal : forall T h, hshape T h ->
    forall T', ~ step T T'.
Proof.
  intros T h Hshape. induction Hshape; intros T' Hstep;
    inversion Hstep; subst;
    repeat match goal with H : step (TMuI _) _ |- _ => inversion H end;
    repeat match goal with H : step (TMuS _) _ |- _ => inversion H end.
Qed.

Lemma hshape_tag_unique : forall T h1 h2,
    hshape T h1 -> hshape T h2 -> h1 = h2.
Proof.
  intros T h1 h2 H1 H2. inversion H1; subst; inversion H2; reflexivity.
Qed.

Lemma eval_from_hshape : forall T h V,
    hshape T h -> eval T V -> V = T.
Proof.
  intros T h V Hshape Heval. inversion Heval; subst; [reflexivity |].
  exfalso. eapply hshape_step_normal; eassumption.
Qed.

Lemma hshape_whd_tag_unique : forall T h0 h,
    hshape T h0 -> whd T h -> h = h0.
Proof.
  intros T h0 h H0 [T' [He H']].
  pose proof (eval_from_hshape T h0 T' H0 He) as HT.
  subst T'. eapply hshape_tag_unique; eassumption.
Qed.

Lemma whd_sort_tag : forall k h, whd (TSort k) h -> h = HSort.
Proof.
  intros k h. apply hshape_whd_tag_unique with (h0 := HSort); constructor.
Qed.

Lemma whd_pi_tag : forall A B h, whd (TPi A B) h -> h = HPi.
Proof.
  intros A B h. apply hshape_whd_tag_unique with (h0 := HPi); constructor.
Qed.

Lemma whd_enumt_tag : forall E h, whd (TEnumT E) h -> h = HEnumT.
Proof.
  intros E h. apply hshape_whd_tag_unique with (h0 := HEnumT); constructor.
Qed.

Lemma whd_conse_tag : forall tg E h, whd (TConsE tg E) h -> h = HConsE.
Proof.
  intros tg E h. apply hshape_whd_tag_unique with (h0 := HConsE); constructor.
Qed.

Lemma whd_muiapp_tag : forall R i h,
    whd (TApp (TMuI R) i) h -> h = HMuIApp.
Proof.
  intros R i h.
  apply hshape_whd_tag_unique with (h0 := HMuIApp); constructor.
Qed.

Lemma whd_musapp_tag : forall Sf i h,
    whd (TApp (TMuS Sf) i) h -> h = HMuSApp.
Proof.
  intros Sf i h.
  apply hshape_whd_tag_unique with (h0 := HMuSApp); constructor.
Qed.

(* A literal fixed-point former synthesizes a Π ending in [Set_0], so its
   first application synthesizes exactly [Set_0].  This is the
   synthesis-only leaf used later by the checking inversion. *)
Lemma eval_pi_sort : forall t v, eval t v -> forall IT A B,
    t = TPi IT (TSort 0) -> v = TPi A B -> B = TSort 0.
Proof.
  intros t v H. induction H; intros IT A B Ht Hv.
  - rewrite Ht in Hv. inversion Hv; subst; reflexivity.
  - inversion Ht; subst. inversion H; subst; eauto.
Qed.

Lemma mui_app_synth_sort : forall R i A,
    value (TApp (TMuI R) i) ->
    synth [] (TApp (TMuI R) i) A -> A = TSort 0.
Proof.
  intros R i A Hv Hs. inversion Hs; subst.
  match goal with Hf : synth [] (TMuI R) ?C |- _ => inversion Hf; subst end.
  match goal with He : eval (TPi _ (TSort 0)) (TPi _ ?B) |- _ =>
    pose proof (eval_pi_sort _ _ He _ _ _ eq_refl eq_refl) as HB;
    rewrite HB; cbn; reflexivity
  end.
Qed.

Lemma mus_app_synth_sort : forall Sf i A,
    value (TApp (TMuS Sf) i) ->
    synth [] (TApp (TMuS Sf) i) A -> A = TSort 0.
Proof.
  intros Sf i A Hv Hs. inversion Hs; subst.
  match goal with Hf : synth [] (TMuS Sf) ?C |- _ => inversion Hf; subst end.
  match goal with He : eval (TPi _ (TSort 0)) (TPi _ ?B) |- _ =>
    pose proof (eval_pi_sort _ _ He _ _ _ eq_refl eq_refl) as HB;
    rewrite HB; cbn; reflexivity
  end.
Qed.

Lemma value_app_synth_sort : forall f a A,
    value (TApp f a) -> synth [] (TApp f a) A -> A = TSort 0.
Proof.
  intros f a A Hv Hs. inversion Hv; subst;
    eauto using mui_app_synth_sort, mus_app_synth_sort.
Qed.

(* Every checking derivation for an application has either its synthesis
   result or the result type chosen by App-check as an origin, followed only
   by subtyping/conversion. *)
Inductive app_origin (f a : term) : term -> Prop :=
| ao_syn : forall C,
    synth [] (TApp f a) C -> app_origin f a C
| ao_chk : forall A B k,
    check [] (TPi A B) (TSort k) ->
    check [] f (TPi A B) ->
    check [] a A ->
    app_origin f a (subst a 0 B).

Lemma check_app_origin : forall G t T, check G t T -> G = [] ->
    forall f a, t = TApp f a ->
    exists X, app_origin f a X /\ sub [] X T.
Proof.
  intros G t T Hck. induction Hck; intros HG f0 a0 Heq;
    try discriminate; inversion Heq; subst.
  - exists A. split; [apply ao_syn; exact H | apply su_conv; exact H0].
  - destruct (IHHck eq_refl f0 a0 eq_refl) as [X [HX HXA]].
    exists X. split; [exact HX |].
    eapply su_trans; eassumption.
  - destruct (IHHck eq_refl f0 a0 eq_refl) as [X [HX HXT]].
    exists X. split; [exact HX |].
    eapply su_trans; [exact HXT | apply su_conv, cv_sym; exact H].
  - exists (subst a0 0 B). split.
    + match goal with
      | H1 : check [] (TPi ?A ?B) (TSort ?k),
        H2 : check [] ?f (TPi ?A ?B),
        H3 : check [] ?a ?A |- _ =>
          eapply ao_chk; [exact H1 | exact H2 | exact H3]
      end.
    + apply su_conv, cv_refl.
  all: try discriminate.
Qed.

Lemma tlnil_step_normal : forall A t, ~ step (TLNil A) t.
Proof. intros A t H; inversion H. Qed.

Lemma tlcons_step_normal : forall A a l t, ~ step (TLCons A a l) t.
Proof. intros A a l t H; inversion H. Qed.

Lemma eval_tlnil_refl : forall A v,
    eval (TLNil A) v -> v = TLNil A.
Proof.
  intros A v H. inversion H; subst; [reflexivity |].
  exfalso. eapply tlnil_step_normal; eassumption.
Qed.

Lemma eval_tlcons_refl : forall A a l v,
    eval (TLCons A a l) v -> v = TLCons A a l.
Proof.
  intros A a l v H. inversion H; subst; [reflexivity |].
  exfalso. eapply tlcons_step_normal; eassumption.
Qed.

Lemma whd_tlnil_impossible : forall A h, ~ whd (TLNil A) h.
Proof.
  intros A h [v [He Hv]].
  pose proof (eval_tlnil_refl A v He) as ->.
  inversion Hv.
Qed.

(* ------------------------------------------------------------------ *)
(*  Full contextual reduction                                         *)
(* ------------------------------------------------------------------ *)

(* [step] is deliberately weak-head.  Conversion closes it under every
   term context and also contains eta.  Making that oriented closure
   explicit gives the reduction whose Church--Rosser theorem is used below. *)
Inductive fstep : term -> term -> Prop :=
| fs_step : forall t u, step t u -> fstep t u
| fs_eta : forall f, fstep (TLam (TApp (lift 1 0 f) (TVar 0))) f
| fs_pi1 : forall A A' B, fstep A A' -> fstep (TPi A B) (TPi A' B)
| fs_pi2 : forall A B B', fstep B B' -> fstep (TPi A B) (TPi A B')
| fs_lam : forall b b', fstep b b' -> fstep (TLam b) (TLam b')
| fs_app1 : forall f f' a, fstep f f' -> fstep (TApp f a) (TApp f' a)
| fs_app2 : forall f a a', fstep a a' -> fstep (TApp f a) (TApp f a')
| fs_sigma1 : forall A A' B, fstep A A' -> fstep (TSigma A B) (TSigma A' B)
| fs_sigma2 : forall A B B', fstep B B' -> fstep (TSigma A B) (TSigma A B')
| fs_pair1 : forall a a' b, fstep a a' -> fstep (TPair a b) (TPair a' b)
| fs_pair2 : forall a b b', fstep b b' -> fstep (TPair a b) (TPair a b')
| fs_fst : forall p p', fstep p p' -> fstep (TFst p) (TFst p')
| fs_snd : forall p p', fstep p p' -> fstep (TSnd p) (TSnd p')
| fs_conse1 : forall t t' E, fstep t t' -> fstep (TConsE t E) (TConsE t' E)
| fs_conse2 : forall t E E', fstep E E' -> fstep (TConsE t E) (TConsE t E')
| fs_enumt : forall E E', fstep E E' -> fstep (TEnumT E) (TEnumT E')
| fs_esucc : forall n n', fstep n n' -> fstep (TESucc n) (TESucc n')
| fs_epi1 : forall E E' P, fstep E E' -> fstep (TEPi E P) (TEPi E' P)
| fs_epi2 : forall E P P', fstep P P' -> fstep (TEPi E P) (TEPi E P')
| fs_switch1 : forall E E' P p e, fstep E E' ->
    fstep (TSwitch E P p e) (TSwitch E' P p e)
| fs_switch2 : forall E P P' p e, fstep P P' ->
    fstep (TSwitch E P p e) (TSwitch E P' p e)
| fs_switch3 : forall E P p p' e, fstep p p' ->
    fstep (TSwitch E P p e) (TSwitch E P p' e)
| fs_switch4 : forall E P p e e', fstep e e' ->
    fstep (TSwitch E P p e) (TSwitch E P p e')
| fs_idesc : forall IT IT', fstep IT IT' -> fstep (TIDesc IT) (TIDesc IT')
| fs_ivar : forall i i', fstep i i' -> fstep (TIVar i) (TIVar i')
| fs_iprod1 : forall A A' B, fstep A A' -> fstep (TIProd A B) (TIProd A' B)
| fs_iprod2 : forall A B B', fstep B B' -> fstep (TIProd A B) (TIProd A B')
| fs_ipi1 : forall S S' T, fstep S S' -> fstep (TIPi S T) (TIPi S' T)
| fs_ipi2 : forall S T T', fstep T T' -> fstep (TIPi S T) (TIPi S T')
| fs_isig1 : forall S S' T, fstep S S' -> fstep (TISig S T) (TISig S' T)
| fs_isig2 : forall S T T', fstep T T' -> fstep (TISig S T) (TISig S T')
| fs_ichoice1 : forall E E' T, fstep E E' ->
    fstep (TIChoice E T) (TIChoice E' T)
| fs_ichoice2 : forall E T T', fstep T T' ->
    fstep (TIChoice E T) (TIChoice E T')
| fs_interp1 : forall D D' X, fstep D D' -> fstep (TInterp D X) (TInterp D' X)
| fs_interp2 : forall D X X', fstep X X' -> fstep (TInterp D X) (TInterp D X')
| fs_mui : forall R R', fstep R R' -> fstep (TMuI R) (TMuI R')
| fs_mus : forall S S', fstep S S' -> fstep (TMuS S) (TMuS S')
| fs_in : forall x x', fstep x x' -> fstep (TIn x) (TIn x')
| fs_ind1 : forall R R' P s i x, fstep R R' ->
    fstep (TInd R P s i x) (TInd R' P s i x)
| fs_ind2 : forall R P P' s i x, fstep P P' ->
    fstep (TInd R P s i x) (TInd R P' s i x)
| fs_ind3 : forall R P s s' i x, fstep s s' ->
    fstep (TInd R P s i x) (TInd R P s' i x)
| fs_ind4 : forall R P s i i' x, fstep i i' ->
    fstep (TInd R P s i x) (TInd R P s i' x)
| fs_ind5 : forall R P s i x x', fstep x x' ->
    fstep (TInd R P s i x) (TInd R P s i x')
| fs_iall1 : forall D D' X xs P, fstep D D' ->
    fstep (TIAll D X xs P) (TIAll D' X xs P)
| fs_iall2 : forall D X X' xs P, fstep X X' ->
    fstep (TIAll D X xs P) (TIAll D X' xs P)
| fs_iall3 : forall D X xs xs' P, fstep xs xs' ->
    fstep (TIAll D X xs P) (TIAll D X xs' P)
| fs_iall4 : forall D X xs P P', fstep P P' ->
    fstep (TIAll D X xs P) (TIAll D X xs P')
| fs_hyps1 : forall D D' X P h xs, fstep D D' ->
    fstep (THyps D X P h xs) (THyps D' X P h xs)
| fs_hyps2 : forall D X X' P h xs, fstep X X' ->
    fstep (THyps D X P h xs) (THyps D X' P h xs)
| fs_hyps3 : forall D X P P' h xs, fstep P P' ->
    fstep (THyps D X P h xs) (THyps D X P' h xs)
| fs_hyps4 : forall D X P h h' xs, fstep h h' ->
    fstep (THyps D X P h xs) (THyps D X P h' xs)
| fs_hyps5 : forall D X P h xs xs', fstep xs xs' ->
    fstep (THyps D X P h xs) (THyps D X P h xs')
| fs_list : forall A A', fstep A A' -> fstep (TList A) (TList A')
| fs_lnil : forall A A', fstep A A' -> fstep (TLNil A) (TLNil A')
| fs_lcons1 : forall A A' a l, fstep A A' ->
    fstep (TLCons A a l) (TLCons A' a l)
| fs_lcons2 : forall A a a' l, fstep a a' ->
    fstep (TLCons A a l) (TLCons A a' l)
| fs_lcons3 : forall A a l l', fstep l l' ->
    fstep (TLCons A a l) (TLCons A a l')
| fs_case1 : forall M M' Q bs, fstep M M' ->
    fstep (TCase M Q bs) (TCase M' Q bs)
| fs_case2 : forall M Q Q' bs, fstep Q Q' ->
    fstep (TCase M Q bs) (TCase M Q' bs)
| fs_case_br1 : forall M Q bs1 c c' b bs2, fstep c c' ->
    fstep (TCase M Q (bs1 ++ (c, b) :: bs2))
          (TCase M Q (bs1 ++ (c', b) :: bs2))
| fs_case_br2 : forall M Q bs1 c b b' bs2, fstep b b' ->
    fstep (TCase M Q (bs1 ++ (c, b) :: bs2))
          (TCase M Q (bs1 ++ (c, b') :: bs2)).

(* Parallel beta/computation reduction.  Eta is kept separate below; this
   relation contracts any collection of old redexes at once. *)
Inductive pstep : term -> term -> Prop :=
| ps_var : forall n, pstep (TVar n) (TVar n)
| ps_sort : forall k, pstep (TSort k) (TSort k)
| ps_pi : forall A A' B B', pstep A A' -> pstep B B' ->
    pstep (TPi A B) (TPi A' B')
| ps_lam : forall b b', pstep b b' -> pstep (TLam b) (TLam b')
| ps_app : forall f f' a a', pstep f f' -> pstep a a' ->
    pstep (TApp f a) (TApp f' a')
| ps_sigma : forall A A' B B', pstep A A' -> pstep B B' ->
    pstep (TSigma A B) (TSigma A' B')
| ps_pair : forall a a' b b', pstep a a' -> pstep b b' ->
    pstep (TPair a b) (TPair a' b')
| ps_fst : forall p p', pstep p p' -> pstep (TFst p) (TFst p')
| ps_snd : forall p p', pstep p p' -> pstep (TSnd p) (TSnd p')
| ps_unitt : pstep TUnitT TUnitT
| ps_unit : pstep TUnit TUnit
| ps_uid : pstep TUId TUId
| ps_tag : forall s, pstep (TTag s) (TTag s)
| ps_enumu : pstep TEnumU TEnumU
| ps_nile : pstep TNilE TNilE
| ps_conse : forall t t' E E', pstep t t' -> pstep E E' ->
    pstep (TConsE t E) (TConsE t' E')
| ps_enumt : forall E E', pstep E E' -> pstep (TEnumT E) (TEnumT E')
| ps_ezero : pstep TEZero TEZero
| ps_esucc : forall n n', pstep n n' -> pstep (TESucc n) (TESucc n')
| ps_epi : forall E E' P P', pstep E E' -> pstep P P' ->
    pstep (TEPi E P) (TEPi E' P')
| ps_switch : forall E E' P P' p p' e e',
    pstep E E' -> pstep P P' -> pstep p p' -> pstep e e' ->
    pstep (TSwitch E P p e) (TSwitch E' P' p' e')
| ps_idesc : forall I I', pstep I I' -> pstep (TIDesc I) (TIDesc I')
| ps_ivar : forall i i', pstep i i' -> pstep (TIVar i) (TIVar i')
| ps_i1 : pstep TI1 TI1
| ps_iprod : forall A A' B B', pstep A A' -> pstep B B' ->
    pstep (TIProd A B) (TIProd A' B')
| ps_ipi : forall S S' T T', pstep S S' -> pstep T T' ->
    pstep (TIPi S T) (TIPi S' T')
| ps_isig : forall S S' T T', pstep S S' -> pstep T T' ->
    pstep (TISig S T) (TISig S' T')
| ps_ichoice : forall E E' T T', pstep E E' -> pstep T T' ->
    pstep (TIChoice E T) (TIChoice E' T')
| ps_interp : forall D D' X X', pstep D D' -> pstep X X' ->
    pstep (TInterp D X) (TInterp D' X')
| ps_mui : forall R R', pstep R R' -> pstep (TMuI R) (TMuI R')
| ps_mus : forall S S', pstep S S' -> pstep (TMuS S) (TMuS S')
| ps_in : forall x x', pstep x x' -> pstep (TIn x) (TIn x')
| ps_ind : forall R R' P P' s s' i i' x x',
    pstep R R' -> pstep P P' -> pstep s s' -> pstep i i' -> pstep x x' ->
    pstep (TInd R P s i x) (TInd R' P' s' i' x')
| ps_iall : forall D D' X X' xs xs' P P',
    pstep D D' -> pstep X X' -> pstep xs xs' -> pstep P P' ->
    pstep (TIAll D X xs P) (TIAll D' X' xs' P')
| ps_hyps : forall D D' X X' P P' h h' xs xs',
    pstep D D' -> pstep X X' -> pstep P P' -> pstep h h' -> pstep xs xs' ->
    pstep (THyps D X P h xs) (THyps D' X' P' h' xs')
| ps_list : forall A A', pstep A A' -> pstep (TList A) (TList A')
| ps_lnil : forall A A', pstep A A' -> pstep (TLNil A) (TLNil A')
| ps_lcons : forall A A' a a' l l',
    pstep A A' -> pstep a a' -> pstep l l' ->
    pstep (TLCons A a l) (TLCons A' a' l')
| ps_case : forall M M' Q Q' bs bs',
    pstep M M' -> pstep Q Q' -> pbranches bs bs' ->
    pstep (TCase M Q bs) (TCase M' Q' bs')

(* root contractions, with every metavariable developed in parallel *)
| ps_beta : forall b b' a a', pstep b b' -> pstep a a' ->
    pstep (TApp (TLam b) a) (subst a' 0 b')
| ps_fst_pair : forall a a' b b', pstep a a' -> pstep b b' ->
    pstep (TFst (TPair a b)) a'
| ps_snd_pair : forall a a' b b', pstep a a' -> pstep b b' ->
    pstep (TSnd (TPair a b)) b'
| ps_epi_nil : forall P P', pstep P P' -> pstep (TEPi TNilE P) TUnitT
| ps_epi_cons : forall tg tg' E E' P P',
    pstep tg tg' -> pstep E E' -> pstep P P' ->
    pstep (TEPi (TConsE tg E) P)
      (TSigma (TApp P' TEZero)
        (lift 1 0 (TEPi E' (TLam (TApp (lift 1 0 P') (TESucc (TVar 0)))))))
| ps_switch_zero : forall tg tg' E E' P P' p0 p0' ps ps',
    pstep tg tg' -> pstep E E' -> pstep P P' ->
    pstep p0 p0' -> pstep ps ps' ->
    pstep (TSwitch (TConsE tg E) P (TPair p0 ps) TEZero) p0'
| ps_switch_succ : forall tg tg' E E' P P' p0 p0' ps ps' n n',
    pstep tg tg' -> pstep E E' -> pstep P P' ->
    pstep p0 p0' -> pstep ps ps' -> pstep n n' ->
    pstep (TSwitch (TConsE tg E) P (TPair p0 ps) (TESucc n))
      (TSwitch E' (TLam (TApp (lift 1 0 P') (TESucc (TVar 0)))) ps' n')
| ps_interp_var : forall i i' X X', pstep i i' -> pstep X X' ->
    pstep (TInterp (TIVar i) X) (TApp X' i')
| ps_interp_one : forall X X', pstep X X' ->
    pstep (TInterp TI1 X) TUnitT
| ps_interp_prod : forall A A' B B' X X',
    pstep A A' -> pstep B B' -> pstep X X' ->
    pstep (TInterp (TIProd A B) X)
      (TSigma (TInterp A' X') (lift 1 0 (TInterp B' X')))
| ps_interp_pi : forall S S' T T' X X',
    pstep S S' -> pstep T T' -> pstep X X' ->
    pstep (TInterp (TIPi S T) X)
      (TPi S' (TInterp (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')))
| ps_interp_sig : forall S S' T T' X X',
    pstep S S' -> pstep T T' -> pstep X X' ->
    pstep (TInterp (TISig S T) X)
      (TSigma S' (TInterp (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')))
| ps_interp_choice : forall E E' T T' X X',
    pstep E E' -> pstep T T' -> pstep X X' ->
    pstep (TInterp (TIChoice E T) X)
      (TSigma (TEnumT E')
        (TInterp (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')))
| ps_iall_var : forall j j' X X' x x' P P',
    pstep j j' -> pstep X X' -> pstep x x' -> pstep P P' ->
    pstep (TIAll (TIVar j) X x P) (TApp P' (TPair j' x'))
| ps_iall_one : forall X X' P P', pstep X X' -> pstep P P' ->
    pstep (TIAll TI1 X TUnit P) TUnitT
| ps_iall_prod : forall A A' B B' X X' a a' b b' P P',
    pstep A A' -> pstep B B' -> pstep X X' ->
    pstep a a' -> pstep b b' -> pstep P P' ->
    pstep (TIAll (TIProd A B) X (TPair a b) P)
      (TSigma (TIAll A' X' a' P') (lift 1 0 (TIAll B' X' b' P')))
| ps_iall_pi : forall S S' T T' X X' f f' P P',
    pstep S S' -> pstep T T' -> pstep X X' -> pstep f f' -> pstep P P' ->
    pstep (TIAll (TIPi S T) X f P)
      (TPi S' (TIAll (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')
                    (TApp (lift 1 0 f') (TVar 0)) (lift 1 0 P')))
| ps_iall_sig : forall S S' T T' X X' s s' x x' P P',
    pstep S S' -> pstep T T' -> pstep X X' ->
    pstep s s' -> pstep x x' -> pstep P P' ->
    pstep (TIAll (TISig S T) X (TPair s x) P)
      (TIAll (TApp T' s') X' x' P')
| ps_iall_choice : forall E E' T T' X X' e e' x x' P P',
    pstep E E' -> pstep T T' -> pstep X X' ->
    pstep e e' -> pstep x x' -> pstep P P' ->
    pstep (TIAll (TIChoice E T) X (TPair e x) P)
      (TIAll (TApp T' e') X' x' P')
| ps_hyps_var : forall j j' X X' P P' h h' x x',
    pstep j j' -> pstep X X' -> pstep P P' -> pstep h h' -> pstep x x' ->
    pstep (THyps (TIVar j) X P h x) (TApp (TApp h' j') x')
| ps_hyps_one : forall X X' P P' h h',
    pstep X X' -> pstep P P' -> pstep h h' ->
    pstep (THyps TI1 X P h TUnit) TUnit
| ps_hyps_prod : forall A A' B B' X X' P P' h h' a a' b b',
    pstep A A' -> pstep B B' -> pstep X X' -> pstep P P' ->
    pstep h h' -> pstep a a' -> pstep b b' ->
    pstep (THyps (TIProd A B) X P h (TPair a b))
      (TPair (THyps A' X' P' h' a') (THyps B' X' P' h' b'))
| ps_hyps_pi : forall S S' T T' X X' P P' h h' f f',
    pstep S S' -> pstep T T' -> pstep X X' -> pstep P P' ->
    pstep h h' -> pstep f f' ->
    pstep (THyps (TIPi S T) X P h f)
      (TLam (THyps (TApp (lift 1 0 T') (TVar 0)) (lift 1 0 X')
                    (lift 1 0 P') (lift 1 0 h')
                    (TApp (lift 1 0 f') (TVar 0))))
| ps_hyps_sig : forall S S' T T' X X' P P' h h' s s' x x',
    pstep S S' -> pstep T T' -> pstep X X' -> pstep P P' ->
    pstep h h' -> pstep s s' -> pstep x x' ->
    pstep (THyps (TISig S T) X P h (TPair s x))
      (THyps (TApp T' s') X' P' h' x')
| ps_hyps_choice : forall E E' T T' X X' P P' h h' e e' x x',
    pstep E E' -> pstep T T' -> pstep X X' -> pstep P P' ->
    pstep h h' -> pstep e e' -> pstep x x' ->
    pstep (THyps (TIChoice E T) X P h (TPair e x))
      (THyps (TApp T' e') X' P' h' x')
| ps_ind_red : forall R R' P P' s s' i i' xs xs',
    pstep R R' -> pstep P P' -> pstep s s' -> pstep i i' -> pstep xs xs' ->
    pstep (TInd R P s i (TIn xs))
      (TApp (TApp (TApp s' i') xs')
        (THyps (TApp R' i') (TMuI R') P'
          (TLam (TLam (TInd (lift 2 0 R') (lift 2 0 P') (lift 2 0 s')
                            (TVar 1) (TVar 0)))) xs'))
| ps_case_red : forall a xs xs' Q bs k c b b' n,
    nth_error bs k = Some (c,b) -> enum_pos c n -> enum_pos a n ->
    (forall j cj bj, j < k -> nth_error bs j = Some (cj,bj) ->
       exists nj, enum_pos cj nj /\ nj <> n) ->
    pstep xs xs' -> pstep b b' ->
    pstep (TCase (TIn (TPair a xs)) Q bs) (subst xs' 0 b')

with pbranches : list (term * term) -> list (term * term) -> Prop :=
| pbs_nil : pbranches [] []
| pbs_cons : forall c c' b b' bs bs',
    pstep c c' -> pstep b b' -> pbranches bs bs' ->
    pbranches ((c,b)::bs) ((c',b')::bs').

Lemma pbranches_nth_error_rev : forall bs bs' k c' b',
    pbranches bs bs' ->
    nth_error bs' k = Some (c',b') ->
    exists c b, nth_error bs k = Some (c,b) /\
      pstep c c' /\ pstep b b'.
Proof.
  intros bs bs' k c' b' Hpb.
  revert k c' b'.
  induction Hpb as [|c0 c0' b0 b0' bs0 bs0' Hc Hb Htail IH];
    intros k c' b'; destruct k as [|k]; cbn.
  - discriminate.
  - discriminate.
  - intros Hnth. inversion Hnth; subst c' b'.
    exists c0, b0. split; [reflexivity | auto].
  - intros Hnth. apply IH. exact Hnth.
Qed.

Lemma pbranches_nth_error : forall bs bs' k c b,
    pbranches bs bs' ->
    nth_error bs k = Some (c,b) ->
    exists c' b', nth_error bs' k = Some (c',b') /\
      pstep c c' /\ pstep b b'.
Proof.
  intros bs bs' k c b Hpb.
  revert k c b.
  induction Hpb as [|c0 c0' b0 b0' bs0 bs0' Hc Hb Htail IH];
    intros k c b; destruct k as [|k]; cbn.
  - discriminate.
  - discriminate.
  - intros Hnth. inversion Hnth; subst c b.
    exists c0', b0'. split; [reflexivity | auto].
  - intros Hnth. apply IH. exact Hnth.
Qed.

Scheme pstep_ind' := Induction for pstep Sort Prop
with pbranches_ind' := Induction for pbranches Sort Prop.
Combined Scheme pstep_pbranches_ind from pstep_ind', pbranches_ind'.

Lemma pstep_refl : forall t, pstep t t.
Proof.
  apply (tsize_strong_ind (fun t => pstep t t)).
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
  | IH : forall u, tsize u < tsize (TCase ?M ?Q ?bs) -> pstep u u
      |- pbranches ?bs ?bs =>
      assert (HB : forall c b, In (c,b) bs -> pstep c c /\ pstep b b)
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

Lemma pbranches_refl : forall bs, pbranches bs bs.
Proof.
  induction bs as [|[c b] bs IH].
  - constructor.
  - constructor; try apply pstep_refl; exact IH.
Qed.

Lemma pbranches_replace_label : forall bs1 c c' b bs2,
    pstep c c' ->
    pbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c',b) :: bs2).
Proof.
  induction bs1 as [|[d e] bs1 IH]; intros c c' b bs2 Hcc'; cbn.
  - constructor; [exact Hcc' | apply pstep_refl | apply pbranches_refl].
  - constructor;
      [apply pstep_refl | apply pstep_refl | apply IH; exact Hcc'].
Qed.

Lemma step_pstep : forall t u, step t u -> pstep t u.
Proof.
  intros t u H.
  induction H;
    try solve [constructor; eauto using pstep_refl];
    try solve [eapply ps_case; eauto using pstep_refl, pbranches_refl];
    try solve [eapply ps_case; eauto using pstep_refl,
      pbranches_replace_label];
    try solve [eapply ps_case_red; eauto using pstep_refl].
  - eapply ps_fst_pair; eauto using pstep_refl.
  - eapply ps_snd_pair; eauto using pstep_refl.
  - eapply ps_epi_nil; eauto using pstep_refl.
  - eapply ps_epi_cons; eauto using pstep_refl.
  - eapply ps_switch_zero; eauto using pstep_refl.
  - eapply ps_switch_succ; eauto using pstep_refl.
  - eapply ps_interp_one; eauto using pstep_refl.
  - eapply ps_iall_var; eauto using pstep_refl.
  - eapply ps_iall_one; eauto using pstep_refl.
  - eapply ps_iall_sig; eauto using pstep_refl.
  - eapply ps_iall_choice; eauto using pstep_refl.
  - eapply ps_hyps_var; eauto using pstep_refl.
  - eapply ps_hyps_one; eauto using pstep_refl.
  - eapply ps_hyps_pi; eauto using pstep_refl.
  - eapply ps_hyps_sig; eauto using pstep_refl.
  - eapply ps_hyps_choice; eauto using pstep_refl.
Qed.

Lemma pstep_enum_pos_id : forall c c' n,
    pstep c c' -> enum_pos c n -> c' = c.
Proof.
  intros c c' n Hp He.
  revert c' Hp.
  induction He; intros c' Hp.
  - inversion Hp. reflexivity.
  - inversion Hp; subst. f_equal. eapply IHHe. assumption.
Qed.

Lemma pstep_lift_mut :
  (forall t u (H : pstep t u), forall d k,
      pstep (lift d k t) (lift d k u)) /\
  (forall bs bs' (H : pbranches bs bs'), forall d k,
      pbranches
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs')).
Proof.
  apply pstep_pbranches_ind; cbn; intros;
    try solve [constructor; eauto using pstep_refl].
  - apply pstep_refl.
  - rewrite lift_subst_zero_comm. eapply ps_beta; eauto.
  - eapply ps_fst_pair; eauto.
  - eapply ps_snd_pair; eauto.
  - eapply ps_epi_nil; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    repeat rewrite (lift_lift_one_one _ d k).
    repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_epi_cons; eauto.
  - eapply ps_switch_zero; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_switch_succ; eauto.
  - eapply ps_interp_one; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_interp_prod; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_interp_pi; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_interp_sig; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_interp_choice; eauto.
  - eapply ps_iall_var; eauto.
  - eapply ps_iall_one; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_iall_prod; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_iall_pi; eauto.
  - eapply ps_iall_sig; eauto.
  - eapply ps_iall_choice; eauto.
  - eapply ps_hyps_var; eauto.
  - eapply ps_hyps_one; eauto.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply ps_hyps_pi; eauto.
  - eapply ps_hyps_sig; eauto.
  - eapply ps_hyps_choice; eauto.
  - repeat rewrite (lift_lift_two_zero _ d k).
    eapply ps_ind_red; eauto.
  - rewrite lift_subst_zero_comm.
    eapply ps_case_red with
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
Qed.

Corollary pstep_lift : forall t u, pstep t u -> forall d k,
    pstep (lift d k t) (lift d k u).
Proof. intros t u H. exact (proj1 pstep_lift_mut t u H). Qed.

Corollary pbranches_lift : forall bs bs', pbranches bs bs' -> forall d k,
    pbranches
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs').
Proof. intros bs bs' H. exact (proj2 pstep_lift_mut bs bs' H). Qed.

Lemma pstep_subst_mut :
  (forall t t' (H : pstep t t'), forall u u' k,
      pstep u u' -> pstep (subst u k t) (subst u' k t')) /\
  (forall bs bs' (H : pbranches bs bs'), forall u u' k,
      pstep u u' ->
      pbranches
        (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
        (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) bs')).
Proof.
  apply pstep_pbranches_ind; cbn; intros;
    try solve [constructor; eauto using pstep_refl, pstep_lift].
  - change (pstep (subst u k (TVar n)) (subst u' k (TVar n))).
    destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
    + assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
      cbn [subst]. rewrite Hlt. apply pstep_refl.
    + subst n.
      assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
      cbn [subst]. rewrite Hlt, Heq. eapply pstep_lift. exact H.
    + assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
      cbn [subst]. rewrite Hlt, Heq. apply pstep_refl.
  - rewrite subst_subst_zero_comm. eapply ps_beta; eauto.
  - eapply ps_fst_pair; eauto.
  - eapply ps_snd_pair; eauto.
  - eapply ps_epi_nil; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    repeat rewrite (subst_lift_one_one _ u' k).
    repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_epi_cons; eauto.
  - eapply ps_switch_zero; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_switch_succ; eauto.
  - eapply ps_interp_one; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_interp_prod; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_interp_pi; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_interp_sig; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_interp_choice; eauto.
  - eapply ps_iall_var; eauto.
  - eapply ps_iall_one; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_iall_prod; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_iall_pi; eauto.
  - eapply ps_iall_sig; eauto.
  - eapply ps_iall_choice; eauto.
  - eapply ps_hyps_var; eauto.
  - eapply ps_hyps_one; eauto.
  - repeat rewrite (subst_lift_one_zero _ u' k).
    eapply ps_hyps_pi; eauto.
  - eapply ps_hyps_sig; eauto.
  - eapply ps_hyps_choice; eauto.
  - repeat rewrite (subst_lift_two_zero _ u' k).
    eapply ps_ind_red; eauto.
  - rewrite subst_subst_zero_comm.
    eapply ps_case_red with
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
Qed.

Corollary pstep_subst : forall t t', pstep t t' -> forall u u' k,
    pstep u u' -> pstep (subst u k t) (subst u' k t').
Proof. intros t t' H. exact (proj1 pstep_subst_mut t t' H). Qed.

Corollary pbranches_subst : forall bs bs', pbranches bs bs' ->
    forall u u' k, pstep u u' ->
    pbranches
      (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
      (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) bs').
Proof. intros bs bs' H. exact (proj2 pstep_subst_mut bs bs' H). Qed.

Fixpoint enum_index (c : term) : option nat :=
  match c with
  | TEZero => Some 0
  | TESucc d => option_map S (enum_index d)
  | _ => None
  end.

Fixpoint first_branch (n : nat) (bs : list (term * term)) : option term :=
  match bs with
  | [] => None
  | (c,b) :: bs' =>
      match enum_index c with
      | Some m => if Nat.eqb m n then Some b else first_branch n bs'
      | None => None
      end
  end.

Lemma first_branch_map_body : forall (F : term -> term) n bs,
    first_branch n (map (fun '(c,b) => (c, F b)) bs) =
    option_map F (first_branch n bs).
Proof.
  intros F n bs. induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
  destruct (enum_index c); [destruct (Nat.eqb n0 n) |]; cbn;
    auto.
Qed.

Lemma enum_index_sound : forall c n,
    enum_index c = Some n -> enum_pos c n.
Proof.
  intros c. induction c; intros m H; cbn in H; try discriminate.
  - inversion H; constructor.
  - destruct (enum_index c) eqn:He; cbn in H; try discriminate.
    inversion H; subst. constructor. eauto.
Qed.

Lemma enum_index_complete : forall c n,
    enum_pos c n -> enum_index c = Some n.
Proof.
  intros c n H; induction H.
  - reflexivity.
  - cbn.
    match goal with
    | Hih : enum_index _ = Some _ |- _ => rewrite Hih; reflexivity
    end.
Qed.

Lemma first_branch_selected : forall n bs k c b,
    nth_error bs k = Some (c,b) ->
    enum_pos c n ->
    (forall j cj bj, j < k ->
       nth_error bs j = Some (cj,bj) ->
       exists nj, enum_pos cj nj /\ nj <> n) ->
    first_branch n bs = Some b.
Proof.
  intros n bs.
  induction bs as [|[c0 b0] bs IH]; intros k c b Hnth Hpos Hpre.
  - destruct k; cbn in Hnth; discriminate.
  - destruct k as [|k].
    + cbn in Hnth. inversion Hnth; subst c b.
      cbn. rewrite (enum_index_complete c0 n Hpos).
      rewrite Nat.eqb_refl. reflexivity.
    + cbn in Hnth.
      assert (Hhead : exists m, enum_pos c0 m /\ m <> n).
      { eapply (Hpre 0 c0 b0); [lia | reflexivity]. }
      destruct Hhead as [m [Hm Hneq]].
      cbn. rewrite (enum_index_complete c0 m Hm).
      assert (Heq : Nat.eqb m n = false)
        by (apply Nat.eqb_neq; exact Hneq).
      rewrite Heq.
      apply IH with (k:=k) (c:=c) (b:=b).
      * exact Hnth.
      * exact Hpos.
      * intros j cj bj Hj Hnthj.
        eapply (Hpre (S j) cj bj); [lia | cbn; exact Hnthj].
Qed.

Lemma first_branch_some : forall n bs b,
    first_branch n bs = Some b ->
    exists k c,
      nth_error bs k = Some (c,b) /\
      enum_pos c n /\
      (forall j cj bj, j < k ->
         nth_error bs j = Some (cj,bj) ->
         exists nj, enum_pos cj nj /\ nj <> n).
Proof.
  intros n bs. induction bs as [|[c0 b0] bs IH]; intros b Hfirst.
  - discriminate.
  - cbn in Hfirst.
    destruct (enum_index c0) as [m|] eqn:Hidx; [|discriminate].
    destruct (Nat.eqb m n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst m. inversion Hfirst; subst b.
      exists 0, c0. split.
      * reflexivity.
      * split.
        -- eapply enum_index_sound. exact Hidx.
        -- intros j cj bj Hj. lia.
    + destruct (IH b Hfirst) as [k [c [Hnth [Hpos Hpre]]]].
      exists (S k), c. split.
      * cbn. exact Hnth.
      * split.
        -- exact Hpos.
        -- intros j cj bj Hj Hnthj. destruct j as [|j].
           ++ cbn in Hnthj. inversion Hnthj; subst cj bj.
              exists m. split.
              ** eapply enum_index_sound. exact Hidx.
              ** apply Nat.eqb_neq in Heq. exact Heq.
           ++ cbn in Hnthj.
              apply Hpre with (j:=j) (cj:=cj) (bj:=bj);
                [lia | exact Hnthj].
Qed.

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
  | TEPi TNilE _ => TUnitT
  | TEPi (TConsE tg E) P =>
      TSigma (TApp (pdev P) TEZero)
        (lift 1 0
          (TEPi (pdev E)
            (TLam (TApp (lift 1 0 (pdev P)) (TESucc (TVar 0))))))
  | TEPi E P => TEPi (pdev E) (pdev P)
  | TSwitch (TConsE tg E) P (TPair p0 ps) TEZero => pdev p0
  | TSwitch (TConsE tg E) P (TPair p0 ps) (TESucc n) =>
      TSwitch (pdev E)
        (TLam (TApp (lift 1 0 (pdev P)) (TESucc (TVar 0))))
        (pdev ps) (pdev n)
  | TSwitch E P p e => TSwitch (pdev E) (pdev P) (pdev p) (pdev e)
  | TIDesc IT => TIDesc (pdev IT)
  | TIVar i => TIVar (pdev i)
  | TI1 => TI1
  | TIProd A B => TIProd (pdev A) (pdev B)
  | TIPi Sd T => TIPi (pdev Sd) (pdev T)
  | TISig Sd T => TISig (pdev Sd) (pdev T)
  | TIChoice E T => TIChoice (pdev E) (pdev T)
  | TInterp (TIVar i) X => TApp (pdev X) (pdev i)
  | TInterp TI1 X => TUnitT
  | TInterp (TIProd A B) X =>
      TSigma (TInterp (pdev A) (pdev X))
        (lift 1 0 (TInterp (pdev B) (pdev X)))
  | TInterp (TIPi Sd T) X =>
      TPi (pdev Sd)
        (TInterp (TApp (lift 1 0 (pdev T)) (TVar 0)) (lift 1 0 (pdev X)))
  | TInterp (TISig Sd T) X =>
      TSigma (pdev Sd)
        (TInterp (TApp (lift 1 0 (pdev T)) (TVar 0)) (lift 1 0 (pdev X)))
  | TInterp (TIChoice E T) X =>
      TSigma (TEnumT (pdev E))
        (TInterp (TApp (lift 1 0 (pdev T)) (TVar 0)) (lift 1 0 (pdev X)))
  | TInterp D X => TInterp (pdev D) (pdev X)
  | TMuI R => TMuI (pdev R)
  | TMuS Sf => TMuS (pdev Sf)
  | TIn x => TIn (pdev x)
  | TInd R P s i (TIn xs) =>
      TApp (TApp (TApp (pdev s) (pdev i)) (pdev xs))
        (THyps (TApp (pdev R) (pdev i)) (TMuI (pdev R)) (pdev P)
          (TLam (TLam
            (TInd (lift 2 0 (pdev R)) (lift 2 0 (pdev P))
                  (lift 2 0 (pdev s)) (TVar 1) (TVar 0)))) (pdev xs))
  | TInd R P s i x => TInd (pdev R) (pdev P) (pdev s) (pdev i) (pdev x)
  | TIAll (TIVar j) X x P => TApp (pdev P) (TPair (pdev j) (pdev x))
  | TIAll TI1 X TUnit P => TUnitT
  | TIAll (TIProd A B) X (TPair a b) P =>
      TSigma (TIAll (pdev A) (pdev X) (pdev a) (pdev P))
        (lift 1 0 (TIAll (pdev B) (pdev X) (pdev b) (pdev P)))
  | TIAll (TIPi Sd T) X f P =>
      TPi (pdev Sd)
        (TIAll (TApp (lift 1 0 (pdev T)) (TVar 0)) (lift 1 0 (pdev X))
          (TApp (lift 1 0 (pdev f)) (TVar 0)) (lift 1 0 (pdev P)))
  | TIAll (TISig Sd T) X (TPair s x) P =>
      TIAll (TApp (pdev T) (pdev s)) (pdev X) (pdev x) (pdev P)
  | TIAll (TIChoice E T) X (TPair e x) P =>
      TIAll (TApp (pdev T) (pdev e)) (pdev X) (pdev x) (pdev P)
  | TIAll D X xs P => TIAll (pdev D) (pdev X) (pdev xs) (pdev P)
  | THyps (TIVar j) X P h x => TApp (TApp (pdev h) (pdev j)) (pdev x)
  | THyps TI1 X P h TUnit => TUnit
  | THyps (TIProd A B) X P h (TPair a b) =>
      TPair (THyps (pdev A) (pdev X) (pdev P) (pdev h) (pdev a))
            (THyps (pdev B) (pdev X) (pdev P) (pdev h) (pdev b))
  | THyps (TIPi Sd T) X P h f =>
      TLam (THyps (TApp (lift 1 0 (pdev T)) (TVar 0)) (lift 1 0 (pdev X))
              (lift 1 0 (pdev P)) (lift 1 0 (pdev h))
              (TApp (lift 1 0 (pdev f)) (TVar 0)))
  | THyps (TISig Sd T) X P h (TPair s x) =>
      THyps (TApp (pdev T) (pdev s)) (pdev X) (pdev P) (pdev h) (pdev x)
  | THyps (TIChoice E T) X P h (TPair e x) =>
      THyps (TApp (pdev T) (pdev e)) (pdev X) (pdev P) (pdev h) (pdev x)
  | THyps D X P h xs =>
      THyps (pdev D) (pdev X) (pdev P) (pdev h) (pdev xs)
  | TList A => TList (pdev A)
  | TLNil A => TLNil (pdev A)
  | TLCons A a l => TLCons (pdev A) (pdev a) (pdev l)
  | TCase M Q bs =>
      let bs' := map (fun '(c,b) => (pdev c, pdev b)) bs in
      let bs_sel := map (fun '(c,b) => (c, pdev b)) bs in
      match M with
      | TIn (TPair a xs) =>
          match enum_index a with
          | Some n =>
              match first_branch n bs_sel with
              | Some b' => subst (pdev xs) 0 b'
              | None => TCase (pdev M) (pdev Q) bs'
              end
          | None => TCase (pdev M) (pdev Q) bs'
          end
      | _ => TCase (pdev M) (pdev Q) bs'
      end
  end.

Lemma pdev_enum_pos : forall c n, enum_pos c n -> pdev c = c.
Proof.
  intros c n H; induction H.
  - reflexivity.
  - cbn. f_equal. assumption.
Qed.

Lemma first_branch_selected_pdev : forall n bs k c b,
    nth_error bs k = Some (c,b) ->
    enum_pos c n ->
    (forall j cj bj, j < k ->
       nth_error bs j = Some (cj,bj) ->
       exists nj, enum_pos cj nj /\ nj <> n) ->
    first_branch n
      (map (fun '(c,b) => (pdev c, pdev b)) bs) =
      Some (pdev b).
Proof.
  intros n bs.
  induction bs as [|[c0 b0] bs IH]; intros k c b Hnth Hpos Hpre.
  - destruct k; cbn in Hnth; discriminate.
  - destruct k as [|k].
    + cbn in Hnth. inversion Hnth; subst c b.
      cbn. rewrite (pdev_enum_pos c0 n Hpos).
      rewrite (enum_index_complete c0 n Hpos).
      rewrite Nat.eqb_refl. reflexivity.
    + cbn in Hnth.
      assert (Hhead : exists m, enum_pos c0 m /\ m <> n).
      { eapply (Hpre 0 c0 b0); [lia | reflexivity]. }
      destruct Hhead as [m [Hm Hneq]].
      cbn. rewrite (pdev_enum_pos c0 m Hm).
      rewrite (enum_index_complete c0 m Hm).
      assert (Heq : Nat.eqb m n = false)
        by (apply Nat.eqb_neq; exact Hneq).
      rewrite Heq.
      apply IH with (k:=k) (c:=c) (b:=b).
      * exact Hnth.
      * exact Hpos.
      * intros j cj bj Hj Hnthj.
        eapply (Hpre (S j) cj bj); [lia | cbn; exact Hnthj].
Qed.

Lemma first_branch_selected_pdev_body : forall n bs k c b,
    nth_error bs k = Some (c,b) ->
    enum_pos c n ->
    (forall j cj bj, j < k ->
       nth_error bs j = Some (cj,bj) ->
       exists nj, enum_pos cj nj /\ nj <> n) ->
    first_branch n
      (map (fun '(c,b) => (c, pdev b)) bs) = Some (pdev b).
Proof.
  intros n bs.
  induction bs as [|[c0 b0] bs IH]; intros k c b Hnth Hpos Hpre.
  - destruct k; cbn in Hnth; discriminate.
  - destruct k as [|k].
    + cbn in Hnth. inversion Hnth; subst c b.
      cbn. rewrite (enum_index_complete c0 n Hpos), Nat.eqb_refl.
      reflexivity.
    + cbn in Hnth.
      destruct (Hpre 0 c0 b0 ltac:(lia) eq_refl) as [m [Hm Hneq]].
      cbn. rewrite (enum_index_complete c0 m Hm).
      assert (Heq : Nat.eqb m n = false)
        by (apply Nat.eqb_neq; exact Hneq).
      rewrite Heq.
      apply IH with (k:=k) (c:=c) (b:=b); try assumption.
      intros j cj bj Hj Hnthj.
      eapply (Hpre (S j) cj bj); [lia | cbn; exact Hnthj].
Qed.

Lemma pstep_case_complete_aux : forall M M' Q Q' bs bs',
    pstep M M' -> pstep M' (pdev M) ->
    pstep Q Q' -> pstep Q' (pdev Q) ->
    pbranches bs bs' ->
    pbranches bs' (map (fun '(c,b) => (pdev c, pdev b)) bs) ->
    pstep (TCase M' Q' bs') (pdev (TCase M Q bs)).
Proof.
  intros M M' Q Q' bs bs' HM HMdev HQ HQdev Hbs Hbsdev.
  destruct M; cbn;
    try solve [eapply ps_case; eauto].
  let z := match goal with
    | Hr : pstep (TIn ?z) _ |- _ => constr:(z)
    end in destruct z; cbn;
    try solve [eapply ps_case; eauto].
  inversion HM; subst.
  match goal with Hr : pstep (TPair _ _) _ |- _ =>
    inversion Hr; clear Hr; subst
  end.
  cbn in HMdev. inversion HMdev; subst.
  match goal with Hr : pstep (TPair _ _) (TPair _ _) |- _ =>
    inversion Hr; clear Hr; subst
  end.
  match goal with |- context [enum_index ?aa] =>
    destruct (enum_index aa) as [n|] eqn:Hidx
  end.
  - rewrite first_branch_map_body.
    destruct (first_branch n bs) as [b0|] eqn:Hfirst.
    + destruct (first_branch_some n bs b0 Hfirst)
        as [k [c [Hnth [Hpos Hpre]]]].
      destruct (pbranches_nth_error bs bs' k c b0 Hbs Hnth)
        as [csel [bsel [Hnth' [Hcc' Hbb']]]].
      assert (Hc' : csel = c) by
        (eapply pstep_enum_pos_id; eauto).
      subst csel.
      destruct (pbranches_nth_error bs'
          (map (fun '(c,b) => (pdev c, pdev b)) bs)
          k c bsel Hbsdev Hnth')
        as [cd [bd [Hnthdev [Hccd Hbbd]]]].
      assert (Hmapnth :
        nth_error (map (fun '(c,b) => (pdev c, pdev b)) bs) k =
          Some (pdev c, pdev b0)).
      { rewrite nth_error_map, Hnth. reflexivity. }
      rewrite Hmapnth in Hnthdev. inversion Hnthdev; subst cd bd.
      pose proof (enum_index_sound _ _ Hidx) as Htpos.
      match type of Htpos with enum_pos ?aa n =>
        match goal with Hat : pstep aa ?ta |- _ =>
          assert (Heqa : ta = aa) by
            (eapply pstep_enum_pos_id; [exact Hat | exact Htpos]);
          subst ta
        end
      end.
      eapply ps_case_red with (k:=k) (c:=c) (b:=bsel) (n:=n).
      * exact Hnth'.
      * exact Hpos.
      * exact Htpos.
      * intros j cj' bj' Hj Hnthj'.
        destruct (pbranches_nth_error_rev bs bs' j cj' bj' Hbs Hnthj')
          as [cj [bj [Hnthj [Hcjcj' Hbjbj']]]].
        destruct (Hpre j cj bj Hj Hnthj) as [nj [Hjpos Hneq]].
        assert (Heqcj : cj' = cj) by
          (eapply pstep_enum_pos_id; eauto).
        subst cj'. exists nj. auto.
      * eauto.
      * exact Hbbd.
    + eapply ps_case; eauto.
  - eapply ps_case; eauto.
Qed.

#[local] Hint Constructors pstep pbranches : pdev.
#[local] Hint Resolve pstep_lift pstep_subst : pdev.

Lemma pstep_complete_mut :
  (forall t u (H : pstep t u), pstep u (pdev t)) /\
  (forall bs bs' (H : pbranches bs bs'),
      pbranches bs' (map (fun '(c,b) => (pdev c, pdev b)) bs)).
Proof.
  apply pstep_pbranches_ind; cbn; intros;
    try solve [constructor; eauto using pstep_refl, pstep_lift, pstep_subst].
  - destruct f; cbn;
      try solve [eapply ps_app; eauto].
    inversion p; subst. inversion H; subst.
    eapply ps_beta; eauto.
  - destruct p; cbn;
      try solve [eapply ps_fst; eauto].
    match goal with Hr : pstep (TypeRulesCore.TPair _ _) _ |- _ =>
      inversion Hr; clear Hr; subst
    end.
    cbn in H. inversion H; subst.
    eapply ps_fst_pair; eauto.
  - destruct p; cbn;
      try solve [eapply ps_snd; eauto].
    match goal with Hr : pstep (TypeRulesCore.TPair _ _) _ |- _ =>
      inversion Hr; clear Hr; subst
    end.
    cbn in H. inversion H; subst.
    eapply ps_snd_pair; eauto.
  - destruct E; cbn;
      try solve [eapply ps_epi; eauto].
    + match goal with Hr : pstep TypeRulesCore.TNilE _ |- _ =>
        inversion Hr; clear Hr; subst
      end.
      eapply ps_epi_nil; eauto.
    + match goal with Hr : pstep (TypeRulesCore.TConsE _ _) _ |- _ =>
        inversion Hr; clear Hr; subst
      end.
      cbn in H. inversion H; subst.
      eapply ps_epi_cons; eauto using pstep_lift.
  - destruct E; cbn;
      try solve [eapply ps_switch; eauto].
    destruct p; cbn;
      try solve [eapply ps_switch; eauto].
    destruct e; cbn;
      try solve [eapply ps_switch; eauto].
    + inversion p0; subst. inversion p2; subst. inversion p3; subst.
      cbn in H, H1, H2.
      inversion H; subst. inversion H1; subst. inversion H2; subst.
      eapply ps_switch_zero; eauto.
    + inversion p0; subst. inversion p2; subst. inversion p3; subst.
      cbn in H, H1, H2.
      inversion H; subst. inversion H1; subst. inversion H2; subst.
      eapply ps_switch_succ; eauto using pstep_lift.
  - destruct D; cbn;
      try solve [eapply ps_interp; eauto].
    all: inversion p; subst; cbn in H; inversion H; subst;
      eauto using pstep, pstep_lift.
  - destruct x; cbn;
      try solve [eapply ps_ind; eauto].
    inversion p3; subst. cbn in H3. inversion H3; subst.
    eapply ps_ind_red; eauto using pstep_lift.
  - destruct D; cbn;
      try solve [eapply ps_iall; eauto].
    + inversion p; subst. cbn in H. inversion H; subst.
      eapply ps_iall_var; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_iall; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p1; subst. cbn in H1. inversion H1; subst.
      eapply ps_iall_one; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_iall; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p1; subst. cbn in H1. inversion H1; subst.
      eapply ps_iall_prod; eauto using pstep_lift.
    + inversion p; subst. cbn in H. inversion H; subst.
      eapply ps_iall_pi; eauto using pstep_lift.
    + destruct xs; cbn;
        try solve [eapply ps_iall; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p1; subst. cbn in H1. inversion H1; subst.
      eapply ps_iall_sig; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_iall; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p1; subst. cbn in H1. inversion H1; subst.
      eapply ps_iall_choice; eauto.
  - destruct D; cbn;
      try solve [eapply ps_hyps; eauto].
    + inversion p; subst. cbn in H. inversion H; subst.
      eapply ps_hyps_var; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_hyps; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p3; subst. cbn in H3. inversion H3; subst.
      eapply ps_hyps_one; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_hyps; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p3; subst. cbn in H3. inversion H3; subst.
      eapply ps_hyps_prod; eauto.
    + inversion p; subst. cbn in H. inversion H; subst.
      eapply ps_hyps_pi; eauto using pstep_lift.
    + destruct xs; cbn;
        try solve [eapply ps_hyps; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p3; subst. cbn in H3. inversion H3; subst.
      eapply ps_hyps_sig; eauto.
    + destruct xs; cbn;
        try solve [eapply ps_hyps; eauto].
      inversion p; subst. cbn in H. inversion H; subst.
      inversion p3; subst. cbn in H3. inversion H3; subst.
      eapply ps_hyps_choice; eauto.
  - eapply pstep_case_complete_aux; eauto.
  - exact (pstep_subst b' (pdev b) H a' (pdev a) 0 H0).
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - eauto 30 with pdev.
  - match goal with
    | Hnth : nth_error ?bs0 ?kk = Some (?cc,?bb),
      Hcpos : TypeRulesCore.enum_pos ?cc ?nn,
      Hapos : TypeRulesCore.enum_pos ?aa ?nn |- _ =>
        cbn;
        rewrite (enum_index_complete aa nn Hapos);
        erewrite (first_branch_selected_pdev_body nn bs0 kk cc bb)
          by eauto;
        eapply pstep_subst; eauto
    end.
Qed.

Lemma pstep_complete : forall t u,
    pstep t u -> pstep u (pdev t).
Proof.
  intros t u Htu. exact (proj1 pstep_complete_mut t u Htu).
Qed.

Lemma pstep_diamond : diamond pstep.
Proof.
  intros t u v Htu Htv. exists (pdev t). split;
    eapply pstep_complete; eassumption.
Qed.

Lemma pstep_confluent : confluent pstep.
Proof. apply diamond_rtc_confluent, pstep_diamond. Qed.

Ltac pconv_congr :=
  eauto 12 using cv_refl, cv_pi, cv_lam, cv_app, cv_sigma, cv_pair,
    cv_fst, cv_snd, cv_conse, cv_enumt, cv_esucc, cv_epi, cv_switch,
    cv_idesc, cv_ivar, cv_iprod, cv_ipi, cv_isig, cv_ichoice,
    cv_interp, cv_mui, cv_mus, cv_in, cv_ind, cv_iall, cv_hyps,
    cv_list, cv_lnil, cv_lcons.

Lemma pstep_conv_mut :
  (forall t u (H : pstep t u), conv t u) /\
  (forall bs bs' (H : pbranches bs bs'), forall pre M Q,
      conv (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply pstep_pbranches_ind; intros;
    try solve [pconv_congr].
  all: try solve
    [eapply cv_trans; [pconv_congr | apply cv_step; constructor]].
  - eapply cv_trans.
    + eapply cv_case; eauto.
    + specialize (H1 [] M' Q'). cbn in H1. exact H1.
  - eapply cv_trans with (u := TApp (TLam b') a');
      [pconv_congr | apply cv_step, st_beta].
  - eapply cv_trans with (u := TFst (TPair a' b'));
      [pconv_congr | apply cv_step, st_fst].
  - eapply cv_trans with (u := TSnd (TPair a' b'));
      [pconv_congr | apply cv_step, st_snd].
  - eapply cv_trans with (u := TEPi (TConsE tg' E') P');
      [pconv_congr | apply cv_step, st_epi_cons].
  - eapply cv_trans with
      (u := TSwitch (TConsE tg' E') P' (TPair p0' ps') TEZero);
      [pconv_congr | apply cv_step, st_switch_zero].
  - eapply cv_trans with
      (u := TSwitch (TConsE tg' E') P' (TPair p0' ps') (TESucc n'));
      [pconv_congr | apply cv_step, st_switch_succ].
  - eapply cv_trans with (u := TInterp (TIVar i') X');
      [pconv_congr | apply cv_step, st_interp_var].
  - eapply cv_trans with (u := TInterp (TIProd A' B') X');
      [pconv_congr | apply cv_step, st_interp_prod].
  - eapply cv_trans with (u := TInterp (TIPi S' T') X');
      [pconv_congr | apply cv_step, st_interp_pi].
  - eapply cv_trans with (u := TInterp (TISig S' T') X');
      [pconv_congr | apply cv_step, st_interp_sig].
  - eapply cv_trans with (u := TInterp (TIChoice E' T') X');
      [pconv_congr | apply cv_step, st_interp_choice].
  - eapply cv_trans with (u := TIAll (TIVar j') X' x' P');
      [pconv_congr | apply cv_step, st_iall_var].
  - eapply cv_trans with
      (u := TIAll (TIProd A' B') X' (TPair a' b') P');
      [pconv_congr | apply cv_step, st_iall_prod].
  - eapply cv_trans with (u := TIAll (TIPi S' T') X' f' P');
      [pconv_congr | apply cv_step, st_iall_pi].
  - eapply cv_trans with
      (u := TIAll (TISig S' T') X' (TPair s' x') P');
      [pconv_congr | apply cv_step, st_iall_sig].
  - eapply cv_trans with
      (u := TIAll (TIChoice E' T') X' (TPair e' x') P');
      [pconv_congr | apply cv_step, st_iall_choice].
  - eapply cv_trans with (u := THyps (TIVar j') X' P' h' x');
      [pconv_congr | apply cv_step, st_hyps_var].
  - eapply cv_trans with
      (u := THyps (TIProd A' B') X' P' h' (TPair a' b'));
      [pconv_congr | apply cv_step, st_hyps_prod].
  - eapply cv_trans with (u := THyps (TIPi S' T') X' P' h' f');
      [pconv_congr | apply cv_step, st_hyps_pi].
  - eapply cv_trans with
      (u := THyps (TISig S' T') X' P' h' (TPair s' x'));
      [pconv_congr | apply cv_step, st_hyps_sig].
  - eapply cv_trans with
      (u := THyps (TIChoice E' T') X' P' h' (TPair e' x'));
      [pconv_congr | apply cv_step, st_hyps_choice].
  - eapply cv_trans with (u := TInd R' P' s' i' (TIn xs'));
      [pconv_congr | apply cv_step, st_ind].
  - assert (Hk : k < length bs).
    { apply nth_error_Some. rewrite e. discriminate. }
    pose proof (firstn_skipn_middle k bs e) as Hsplit.
    rewrite <- Hsplit in e2 |- *.
    eapply cv_trans.
    + eapply cv_case; [|apply cv_refl].
      apply cv_in, cv_pair; [apply cv_refl | exact H].
    + eapply cv_trans.
      * apply cv_case_br; [apply cv_refl | exact H0].
      * apply cv_step.
        eapply st_case with (k:=k) (c:=c) (b:=b') (n:=n).
        -- rewrite nth_error_app2; [|rewrite firstn_length; lia].
           rewrite firstn_length, Nat.min_l by lia.
           replace (k - k) with 0 by lia. reflexivity.
        -- exact e0.
        -- exact e1.
        -- intros j cj bj Hj Hnth.
           eapply e2; [exact Hj |].
           rewrite nth_error_app1 in Hnth
             by (rewrite firstn_length, Nat.min_l by lia; exact Hj).
           rewrite nth_error_app1
             by (rewrite firstn_length, Nat.min_l by lia; exact Hj).
           exact Hnth.
  - change (conv
      (TCase M Q (pre ++ (c,b) :: bs))
      (TCase M Q (pre ++ (c',b') :: bs'))).
    eapply cv_trans.
    + apply cv_case_br; eauto.
    + specialize (H1 (pre ++ [(c',b')]) M Q).
      repeat rewrite <- app_assoc in H1. cbn in H1. exact H1.
Qed.


Lemma pstep_conv : forall t u, pstep t u -> conv t u.
Proof. intros t u H. exact (proj1 pstep_conv_mut t u H). Qed.

Lemma psteps_conv : forall t u, rtc pstep t u -> conv t u.
Proof.
  intros t u H. induction H;
    eauto using conv, pstep_conv.
Qed.

Lemma eval_psteps : forall t u, eval t u -> rtc pstep t u.
Proof.
  intros t u H. induction H; [apply rtc_refl |].
  eapply rtc_step; [apply step_pstep; exact H | exact IHeval].
Qed.

Definition pjoin (t u : term) : Prop :=
  exists w, rtc pstep t w /\ rtc pstep u w.

Lemma pjoin_refl : forall t, pjoin t t.
Proof. intros t. exists t. split; apply rtc_refl. Qed.

Lemma pjoin_sym : forall t u, pjoin t u -> pjoin u t.
Proof. intros t u [w [Htw Huw]]. exists w. auto. Qed.

Lemma pjoin_conv : forall t u, pjoin t u -> conv t u.
Proof.
  intros t u [w [Htw Huw]]. eapply cv_trans.
  - apply psteps_conv, Htw.
  - apply cv_sym, psteps_conv, Huw.
Qed.

Lemma pjoin_trans : forall t u v,
    pjoin t u -> pjoin u v -> pjoin t v.
Proof.
  intros t u v [q [Htq Huq]] [r [Hur Hvr]].
  destruct (pstep_confluent u q r Huq Hur) as [w [Hqw Hrw]].
  exists w. split; eapply rtc_trans; eassumption.
Qed.

Lemma pjoin_reduce_left : forall t u t',
    pjoin t u -> rtc pstep t t' -> pjoin t' u.
Proof.
  intros t u t' [q [Htq Huq]] Htt'.
  destruct (pstep_confluent t q t' Htq Htt') as [w [Hqw Ht'w]].
  exists w. split; [exact Ht'w |].
  eapply rtc_trans; eassumption.
Qed.

Lemma pjoin_eval_left : forall t u t',
    pjoin t u -> eval t t' -> pjoin t' u.
Proof.
  intros t u t' Hjoin Heval. eapply pjoin_reduce_left;
    [exact Hjoin | apply eval_psteps; exact Heval].
Qed.

Lemma pjoin_eval_right : forall t u u',
    pjoin t u -> eval u u' -> pjoin t u'.
Proof.
  intros t u u' Hjoin Heval. apply pjoin_sym.
  eapply pjoin_eval_left; [apply pjoin_sym; exact Hjoin | exact Heval].
Qed.

Lemma pstep_lcons_inv : forall A a l u,
    pstep (TLCons A a l) u ->
    exists A' a' l', u = TLCons A' a' l' /\
      pstep A A' /\ pstep a a' /\ pstep l l'.
Proof.
  intros A a l u H. inversion H; subst.
  repeat eexists; repeat split; eauto.
Qed.

Lemma psteps_lcons_inv_gen : forall t u, rtc pstep t u ->
    forall A a l, t = TLCons A a l ->
    exists A' a' l', u = TLCons A' a' l' /\
      rtc pstep A A' /\ rtc pstep a a' /\ rtc pstep l l'.
Proof.
  intros t u H.
  induction H as [x | x y z Hxy Hyz IH].
  - intros A a l Heq. inversion Heq; subst.
    repeat eexists; repeat split; apply rtc_refl.
  - intros A a l Heq. subst x.
    destruct (pstep_lcons_inv _ _ _ _ Hxy)
      as [A1 [a1 [l1 [Heq1 [HA [Ha Hl]]]]]].
    subst y.
    destruct (IH A1 a1 l1 eq_refl)
      as [A2 [a2 [l2 [Heq2 [HA2 [Ha2 Hl2]]]]]].
    subst z.
    repeat eexists; repeat split; eauto using rtc_trans, rtc_one.
Qed.

Lemma psteps_lcons_inv : forall A a l u,
    rtc pstep (TLCons A a l) u ->
    exists A' a' l', u = TLCons A' a' l' /\
      rtc pstep A A' /\ rtc pstep a a' /\ rtc pstep l l'.
Proof.
  intros A a l u H. eapply psteps_lcons_inv_gen; eauto.
Qed.

Lemma pjoin_lcons_inv : forall A1 a1 l1 A2 a2 l2,
    pjoin (TLCons A1 a1 l1) (TLCons A2 a2 l2) ->
    pjoin A1 A2 /\ pjoin a1 a2 /\ pjoin l1 l2.
Proof.
  intros A1 a1 l1 A2 a2 l2 [w [H1 H2]].
  destruct (psteps_lcons_inv _ _ _ _ H1)
    as [A1' [a1' [l1' [Hw1 [HA1 [Ha1 Hl1]]]]]].
  destruct (psteps_lcons_inv _ _ _ _ H2)
    as [A2' [a2' [l2' [Hw2 [HA2 [Ha2 Hl2]]]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' a2' l2'.
  repeat split; unfold pjoin; eauto.
Qed.

Lemma psteps_lnil_inv_gen : forall t u, rtc pstep t u ->
    forall A, t = TLNil A ->
    exists A', u = TLNil A' /\ rtc pstep A A'.
Proof.
  intros t u H.
  induction H as [x | x y z Hxy Hyz IH].
  - intros A Heq. inversion Heq; subst.
    eexists; split; [reflexivity | apply rtc_refl].
  - intros A Heq. subst x. inversion Hxy; subst.
    destruct (IH A' eq_refl) as [A2 [Heq2 HA2]].
    subst z. eexists; split;
      [reflexivity | eauto using rtc_trans, rtc_one].
Qed.

Lemma psteps_lnil_inv : forall A u,
    rtc pstep (TLNil A) u ->
    exists A', u = TLNil A' /\ rtc pstep A A'.
Proof.
  intros A u H. eapply psteps_lnil_inv_gen; eauto.
Qed.

Lemma no_pjoin_lcons_lnil : forall A a l B,
    ~ pjoin (TLCons A a l) (TLNil B).
Proof.
  intros A a l B [w [Hc Hl]].
  destruct (psteps_lcons_inv _ _ _ _ Hc)
    as [A' [a' [l' [Hw _]]]].
  destruct (psteps_lnil_inv _ _ Hl) as [B' [Hw' _]].
  rewrite Hw in Hw'. discriminate.
Qed.

Lemma fstep_conv : forall t u, fstep t u -> conv t u.
Proof.
  intros t u H. induction H; eauto using conv.
  all: try (eapply cv_pi; eauto using conv).
  all: try (eapply cv_app; eauto using conv).
  all: try (eapply cv_sigma; eauto using conv).
  all: try (eapply cv_pair; eauto using conv).
  all: try (eapply cv_conse; eauto using conv).
  all: try (eapply cv_epi; eauto using conv).
  all: try (eapply cv_switch; eauto using conv).
  all: try (eapply cv_iprod; eauto using conv).
  all: try (eapply cv_ipi; eauto using conv).
  all: try (eapply cv_isig; eauto using conv).
  all: try (eapply cv_ichoice; eauto using conv).
  all: try (eapply cv_interp; eauto using conv).
  all: try (eapply cv_ind; eauto using conv).
  all: try (eapply cv_iall; eauto using conv).
  all: try (eapply cv_hyps; eauto using conv).
  all: try (eapply cv_lcons; eauto using conv).
  all: try (eapply cv_case; eauto using conv).
  all: try (eapply cv_case_br; eauto using conv).
Qed.

Inductive fconv : term -> term -> Prop :=
| fc_step : forall t u, fstep t u -> fconv t u
| fc_refl : forall t, fconv t t
| fc_sym : forall t u, fconv t u -> fconv u t
| fc_trans : forall t u v, fconv t u -> fconv u v -> fconv t v.

Lemma fconv_conv : forall t u, fconv t u -> conv t u.
Proof. intros t u H; induction H; eauto using conv, fstep_conv. Qed.

Lemma fconv_map : forall (F : term -> term),
    (forall x y, fstep x y -> fstep (F x) (F y)) ->
    forall x y, fconv x y -> fconv (F x) (F y).
Proof. intros F HF x y H; induction H; eauto using fconv. Qed.

Lemma fconv_map2 : forall (F : term -> term -> term),
    (forall x y z, fstep x y -> fstep (F x z) (F y z)) ->
    (forall z x y, fstep x y -> fstep (F z x) (F z y)) ->
    forall x x' y y', fconv x x' -> fconv y y' ->
      fconv (F x y) (F x' y').
Proof.
  intros F H1 H2 x x' y y' Hx Hy. eapply fc_trans.
  - eapply (fconv_map (fun z => F z y)); eauto.
  - eapply (fconv_map (fun z => F x' z)); eauto.
Qed.

Lemma fconv_map3 : forall (F : term -> term -> term -> term),
    (forall x y a b, fstep x y -> fstep (F x a b) (F y a b)) ->
    (forall a x y b, fstep x y -> fstep (F a x b) (F a y b)) ->
    (forall a b x y, fstep x y -> fstep (F a b x) (F a b y)) ->
    forall a a' b b' c c', fconv a a' -> fconv b b' -> fconv c c' ->
      fconv (F a b c) (F a' b' c').
Proof.
  intros F H1 H2 H3 a a' b b' c c' Ha Hb Hc. eapply fc_trans.
  - eapply (fconv_map (fun z => F z b c)); eauto.
  - eapply fc_trans.
    + eapply (fconv_map (fun z => F a' z c)); eauto.
    + eapply (fconv_map (fun z => F a' b' z)); eauto.
Qed.

Lemma fconv_map4 : forall (F : term -> term -> term -> term -> term),
    (forall x y a b c, fstep x y -> fstep (F x a b c) (F y a b c)) ->
    (forall a x y b c, fstep x y -> fstep (F a x b c) (F a y b c)) ->
    (forall a b x y c, fstep x y -> fstep (F a b x c) (F a b y c)) ->
    (forall a b c x y, fstep x y -> fstep (F a b c x) (F a b c y)) ->
    forall a a' b b' c c' d d',
      fconv a a' -> fconv b b' -> fconv c c' -> fconv d d' ->
      fconv (F a b c d) (F a' b' c' d').
Proof.
  intros F H1 H2 H3 H4 a a' b b' c c' d d' Ha Hb Hc Hd.
  eapply fc_trans.
  - eapply (fconv_map (fun z => F z b c d)); eauto.
  - eapply fc_trans.
    + eapply (fconv_map (fun z => F a' z c d)); eauto.
    + eapply fc_trans.
      * eapply (fconv_map (fun z => F a' b' z d)); eauto.
      * eapply (fconv_map (fun z => F a' b' c' z)); eauto.
Qed.

Lemma fconv_map5 : forall (F : term -> term -> term -> term -> term -> term),
    (forall x y a b c d, fstep x y -> fstep (F x a b c d) (F y a b c d)) ->
    (forall a x y b c d, fstep x y -> fstep (F a x b c d) (F a y b c d)) ->
    (forall a b x y c d, fstep x y -> fstep (F a b x c d) (F a b y c d)) ->
    (forall a b c x y d, fstep x y -> fstep (F a b c x d) (F a b c y d)) ->
    (forall a b c d x y, fstep x y -> fstep (F a b c d x) (F a b c d y)) ->
    forall a a' b b' c c' d d' e e',
      fconv a a' -> fconv b b' -> fconv c c' -> fconv d d' -> fconv e e' ->
      fconv (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F H1 H2 H3 H4 H5 a a' b b' c c' d d' e e' Ha Hb Hc Hd He.
  eapply fc_trans.
  - eapply (fconv_map (fun z => F z b c d e)); eauto.
  - eapply fc_trans.
    + eapply (fconv_map (fun z => F a' z c d e)); eauto.
    + eapply fc_trans.
      * eapply (fconv_map (fun z => F a' b' z d e)); eauto.
      * eapply fc_trans.
        -- eapply (fconv_map (fun z => F a' b' c' z e)); eauto.
        -- eapply (fconv_map (fun z => F a' b' c' d' z)); eauto.
Qed.

Lemma phi_erase_conv : forall t u, conv t u ->
    fconv (phi_erase t) (phi_erase u).
Proof.
  intros t u H. induction H; cbn; eauto using fconv, fstep, phi_erase_step.
  all: try (eapply fconv_map; eauto using fstep).
  all: try (eapply fconv_map2; eauto using fstep).
  all: try (eapply fconv_map3; eauto using fstep).
  all: try (eapply fconv_map4; eauto using fstep).
  all: try (eapply fconv_map5; eauto using fstep).
  all: try (rewrite phi_erase_lift; apply fc_step, fs_eta).
  all: try (repeat rewrite map_app; cbn;
    eapply fconv_map2; eauto using fstep).
  - eapply (fconv_map2
      (fun x y => TCase x y
        (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs)));
      eauto using fstep.
  - repeat rewrite map_app. cbn.
    eapply (fconv_map2
      (fun x y => TCase (phi_erase M) (phi_erase Q)
        (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs1 ++
         (x,y) :: map (fun '(c,b) => (phi_erase c, phi_erase b)) bs2)));
      eauto using fstep.
Qed.

Lemma fconv_pair : forall a a' b b',
    fconv a a' -> fconv b b' -> fconv (TPair a b) (TPair a' b').
Proof.
  intros a a' b b' Ha Hb. eapply fc_trans.
  - eapply (fconv_map (fun x => TPair x b));
      [intros; apply fs_pair1; eassumption | exact Ha].
  - eapply (fconv_map (fun x => TPair a' x));
      [intros; apply fs_pair2; eassumption | exact Hb].
Qed.

Lemma fconv_app : forall f f' a a',
    fconv f f' -> fconv a a' -> fconv (TApp f a) (TApp f' a').
Proof.
  intros f f' a a' Hf Ha. eapply fc_trans.
  - eapply (fconv_map (fun x => TApp x a));
      [intros; apply fs_app1; eassumption | exact Hf].
  - eapply (fconv_map (fun x => TApp f' x));
      [intros; apply fs_app2; eassumption | exact Ha].
Qed.

Lemma eval_fsteps : forall t u, eval t u -> rtc fstep t u.
Proof.
  intros t u H. induction H; [apply rtc_refl |].
  eapply rtc_step; [apply fs_step; exact H | exact IHeval].
Qed.

Lemma hshape_fstep : forall t h, hshape t h ->
    forall u, fstep t u -> hshape u h.
Proof.
  intros t h Hshape u Hred.
  inversion Hred; subst; inversion Hshape; subst; eauto using hshape;
    try (exfalso; eapply hshape_step_normal; eassumption);
    repeat match goal with
    | H : fstep (TMuI _) _ |- _ => inversion H; subst; clear H
    | H : fstep (TMuS _) _ |- _ => inversion H; subst; clear H
    | H : step (TMuI _) _ |- _ => inversion H
    | H : step (TMuS _) _ |- _ => inversion H
    end;
    constructor.
Qed.

Lemma hshape_fsteps : forall t u, rtc fstep t u ->
    forall h, hshape t h -> hshape u h.
Proof.
  intros t u H. induction H; intros h Hshape; eauto using hshape_fstep.
Qed.

Lemma enum_pos_fstep_normal : forall c n, enum_pos c n ->
    forall d, ~ fstep c d.
Proof.
  intros c n Hpos. induction Hpos; intros d Hred.
  - inversion Hred; subst. inversion H.
  - inversion Hred; subst.
    + eapply pos_step_normal; [constructor; exact Hpos | eassumption].
    + eapply IHHpos; eassumption.
Qed.

Lemma enum_pos_fsteps_refl : forall c n, enum_pos c n ->
    forall d, rtc fstep c d -> d = c.
Proof.
  intros c n Hpos d Hred. inversion Hred; subst; [reflexivity |].
  exfalso. eapply enum_pos_fstep_normal; eassumption.
Qed.

Lemma fstep_enumt_inv : forall E u, fstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ fstep E E'.
Proof. intros E u H; inversion H; subst; try solve [inversion H0]; eauto. Qed.

Lemma fsteps_enumt_inv : forall E u, rtc fstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ rtc fstep E E'.
Proof.
  intros E u H. remember (TEnumT E) as t eqn:Ht. revert E Ht.
  induction H; intros E HE; subst.
  - exists E. split; [reflexivity | apply rtc_refl].
  - destruct (fstep_enumt_inv E y H) as [E1 [-> HE1]].
    destruct (IHrtc E1 eq_refl) as [E2 [-> HE2]].
    exists E2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Lemma fstep_pi_inv : forall A B u, fstep (TPi A B) u ->
    (exists A', u = TPi A' B /\ fstep A A') \/
    (exists B', u = TPi A B' /\ fstep B B').
Proof. intros A B u H; inversion H; subst; try solve [inversion H0]; eauto. Qed.

Lemma fsteps_pi_inv : forall A B u, rtc fstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\ rtc fstep A A' /\ rtc fstep B B'.
Proof.
  intros A B u H. remember (TPi A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (fstep_pi_inv A B y H) as [[A1 [-> HA]] | [B1 [-> HB]]].
    + destruct (IHrtc A1 B eq_refl) as [A2 [B2 [-> [HA2 HB2]]]].
      exists A2, B2. repeat split; eauto using rtc_step.
    + destruct (IHrtc A B1 eq_refl) as [A2 [B2 [-> [HA2 HB2]]]].
      exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma fstep_lcons_inv : forall A a l u, fstep (TLCons A a l) u ->
    (exists A', u = TLCons A' a l /\ fstep A A') \/
    (exists a', u = TLCons A a' l /\ fstep a a') \/
    (exists l', u = TLCons A a l' /\ fstep l l').
Proof. intros A a l u H; inversion H; subst; try solve [inversion H0]; eauto. Qed.

Lemma fsteps_lcons_inv : forall A a l u, rtc fstep (TLCons A a l) u ->
    exists A' a' l', u = TLCons A' a' l' /\
      rtc fstep A A' /\ rtc fstep a a' /\ rtc fstep l l'.
Proof.
  intros A a l u H. remember (TLCons A a l) as t eqn:Ht. revert A a l Ht.
  induction H; intros A a l HE; subst.
  - exists A, a, l. repeat split; apply rtc_refl.
  - destruct (fstep_lcons_inv A a l y H)
      as [[A1 [-> HA]] | [[a1 [-> Ha]] | [l1 [-> Hl]]]].
    + destruct (IHrtc A1 a l eq_refl) as [A2 [a2 [l2 [-> [HA2 [Ha2 Hl2]]]]]].
      exists A2, a2, l2. repeat split; eauto using rtc_step.
    + destruct (IHrtc A a1 l eq_refl) as [A2 [a2 [l2 [-> [HA2 [Ha2 Hl2]]]]]].
      exists A2, a2, l2. repeat split; eauto using rtc_step.
    + destruct (IHrtc A a l1 eq_refl) as [A2 [a2 [l2 [-> [HA2 [Ha2 Hl2]]]]]].
      exists A2, a2, l2. repeat split; eauto using rtc_step.
Qed.

(* Checked conversion metatheory: _tmp_epstep *)
Module _tmp_epstep.

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

(* Parallel contextual eta reduction, with no beta/computation roots. *)
Inductive epstep : term -> term -> Prop :=
| eps_var : forall n, epstep (TVar n) (TVar n)
| eps_sort : forall k, epstep (TSort k) (TSort k)
| eps_pi : forall A A' B B', epstep A A' -> epstep B B' ->
    epstep (TPi A B) (TPi A' B')
| eps_lam : forall b b', epstep b b' -> epstep (TLam b) (TLam b')
| eps_app : forall f f' a a', epstep f f' -> epstep a a' ->
    epstep (TApp f a) (TApp f' a')
| eps_sigma : forall A A' B B', epstep A A' -> epstep B B' ->
    epstep (TSigma A B) (TSigma A' B')
| eps_pair : forall a a' b b', epstep a a' -> epstep b b' ->
    epstep (TPair a b) (TPair a' b')
| eps_fst : forall p p', epstep p p' -> epstep (TFst p) (TFst p')
| eps_snd : forall p p', epstep p p' -> epstep (TSnd p) (TSnd p')
| eps_unitt : epstep TUnitT TUnitT
| eps_unit : epstep TUnit TUnit
| eps_uid : epstep TUId TUId
| eps_tag : forall s, epstep (TTag s) (TTag s)
| eps_enumu : epstep TEnumU TEnumU
| eps_nile : epstep TNilE TNilE
| eps_conse : forall t t' E E', epstep t t' -> epstep E E' ->
    epstep (TConsE t E) (TConsE t' E')
| eps_enumt : forall E E', epstep E E' -> epstep (TEnumT E) (TEnumT E')
| eps_ezero : epstep TEZero TEZero
| eps_esucc : forall n n', epstep n n' -> epstep (TESucc n) (TESucc n')
| eps_epi : forall E E' P P', epstep E E' -> epstep P P' ->
    epstep (TEPi E P) (TEPi E' P')
| eps_switch : forall E E' P P' p p' e e',
    epstep E E' -> epstep P P' -> epstep p p' -> epstep e e' ->
    epstep (TSwitch E P p e) (TSwitch E' P' p' e')
| eps_idesc : forall I I', epstep I I' -> epstep (TIDesc I) (TIDesc I')
| eps_ivar : forall i i', epstep i i' -> epstep (TIVar i) (TIVar i')
| eps_i1 : epstep TI1 TI1
| eps_iprod : forall A A' B B', epstep A A' -> epstep B B' ->
    epstep (TIProd A B) (TIProd A' B')
| eps_ipi : forall S S' T T', epstep S S' -> epstep T T' ->
    epstep (TIPi S T) (TIPi S' T')
| eps_isig : forall S S' T T', epstep S S' -> epstep T T' ->
    epstep (TISig S T) (TISig S' T')
| eps_ichoice : forall E E' T T', epstep E E' -> epstep T T' ->
    epstep (TIChoice E T) (TIChoice E' T')
| eps_interp : forall D D' X X', epstep D D' -> epstep X X' ->
    epstep (TInterp D X) (TInterp D' X')
| eps_mui : forall R R', epstep R R' -> epstep (TMuI R) (TMuI R')
| eps_mus : forall S S', epstep S S' -> epstep (TMuS S) (TMuS S')
| eps_in : forall x x', epstep x x' -> epstep (TIn x) (TIn x')
| eps_ind : forall R R' P P' s s' i i' x x',
    epstep R R' -> epstep P P' -> epstep s s' -> epstep i i' -> epstep x x' ->
    epstep (TInd R P s i x) (TInd R' P' s' i' x')
| eps_iall : forall D D' X X' xs xs' P P',
    epstep D D' -> epstep X X' -> epstep xs xs' -> epstep P P' ->
    epstep (TIAll D X xs P) (TIAll D' X' xs' P')
| eps_hyps : forall D D' X X' P P' h h' xs xs',
    epstep D D' -> epstep X X' -> epstep P P' -> epstep h h' -> epstep xs xs' ->
    epstep (THyps D X P h xs) (THyps D' X' P' h' xs')
| eps_list : forall A A', epstep A A' -> epstep (TList A) (TList A')
| eps_lnil : forall A A', epstep A A' -> epstep (TLNil A) (TLNil A')
| eps_lcons : forall A A' a a' l l',
    epstep A A' -> epstep a a' -> epstep l l' ->
    epstep (TLCons A a l) (TLCons A' a' l')
| eps_case : forall M M' Q Q' bs bs',
    epstep M M' -> epstep Q Q' -> epbranches bs bs' ->
    epstep (TCase M Q bs) (TCase M' Q' bs')
| eps_eta : forall f f', epstep f f' ->
    epstep (TLam (TApp (lift 1 0 f) (TVar 0))) f'
with epbranches : list (term * term) -> list (term * term) -> Prop :=
| epbs_nil : epbranches [] []
| epbs_cons : forall c c' b b' bs bs',
    epstep c c' -> epstep b b' -> epbranches bs bs' ->
    epbranches ((c,b)::bs) ((c',b')::bs').

Scheme epstep_ind' := Induction for epstep Sort Prop
with epbranches_ind' := Induction for epbranches Sort Prop.
Combined Scheme epstep_epbranches_ind from epstep_ind', epbranches_ind'.

Lemma epstep_refl : forall t, epstep t t.
Proof.
  apply (tsize_strong_ind (fun t => epstep t t)).
  intros t IH. destruct t;
    try pose proof (tsize_pos t) as Ht;
    try pose proof (tsize_pos t1) as Ht1;
    try pose proof (tsize_pos t2) as Ht2;
    try pose proof (tsize_pos t3) as Ht3;
    try pose proof (tsize_pos t4) as Ht4;
    try pose proof (tsize_pos t5) as Ht5;
    try solve [constructor];
    try (constructor; repeat (apply IH; cbn; lia)).
  induction bs as [|[c b] bs IHbs]; [constructor |].
  constructor.
  - apply IH. eapply tsize_case_bs. left. reflexivity.
  - apply IH. eapply tsize_case_bs_body. left. reflexivity.
  - apply IHbs. intros u Hu. apply IH. cbn in *. lia.
Qed.

Lemma epbranches_refl : forall bs, epbranches bs bs.
Proof.
  induction bs as [|[c b] bs IH]; constructor;
    eauto using epstep_refl.
Qed.

Lemma epstep_lift_mut :
  (forall t u (H : epstep t u), forall d k,
      epstep (lift d k t) (lift d k u)) /\
  (forall bs bs' (H : epbranches bs bs'), forall d k,
      epbranches
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs')).
Proof.
  apply epstep_epbranches_ind; cbn; intros;
    try solve [constructor; eauto using epstep_refl].
  - apply epstep_refl.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply eps_eta; eauto.
Qed.

Corollary epstep_lift : forall t u, epstep t u -> forall d k,
    epstep (lift d k t) (lift d k u).
Proof. intros t u H d k. exact (proj1 epstep_lift_mut t u H d k). Qed.

Corollary epbranches_lift : forall bs bs', epbranches bs bs' -> forall d k,
    epbranches
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs').
Proof. intros bs bs' H d k. exact (proj2 epstep_lift_mut bs bs' H d k). Qed.

End _tmp_epstep.

(* Checked conversion metatheory: _tmp_lower *)
Module _tmp_lower.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations.

Import TypeRulesCore.

Fixpoint lower_bs (f : nat -> term -> option term) (k : nat)
    (bs : list (term * term)) : option (list (term * term)) :=
  match bs with
  | [] => Some []
  | (c,b)::bs' =>
      match f k c, f (S k) b, lower_bs f k bs' with
      | Some c', Some b', Some bs'' => Some ((c',b')::bs'')
      | _, _, _ => None
      end
  end.

Fixpoint lower (k : nat) (t : term) {struct t} : option term :=
  match t with
  | TVar n => if Nat.ltb n k then Some (TVar n)
              else if Nat.eqb n k then None
              else Some (TVar (Nat.pred n))
  | TSort s => Some (TSort s)
  | TPi A B =>
      match lower k A, lower (S k) B with
      | Some A', Some B' => Some (TPi A' B') | _, _ => None end
  | TLam b => option_map TLam (lower (S k) b)
  | TApp f a =>
      match lower k f, lower k a with
      | Some f', Some a' => Some (TApp f' a') | _, _ => None end
  | TSigma A B =>
      match lower k A, lower (S k) B with
      | Some A', Some B' => Some (TSigma A' B') | _, _ => None end
  | TPair a b =>
      match lower k a, lower k b with
      | Some a', Some b' => Some (TPair a' b') | _, _ => None end
  | TFst p => option_map TFst (lower k p)
  | TSnd p => option_map TSnd (lower k p)
  | TUnitT => Some TUnitT
  | TUnit => Some TUnit
  | TUId => Some TUId
  | TTag s => Some (TTag s)
  | TEnumU => Some TEnumU
  | TNilE => Some TNilE
  | TConsE tg E =>
      match lower k tg, lower k E with
      | Some tg', Some E' => Some (TConsE tg' E') | _, _ => None end
  | TEnumT E => option_map TEnumT (lower k E)
  | TEZero => Some TEZero
  | TESucc n => option_map TESucc (lower k n)
  | TEPi E P =>
      match lower k E, lower k P with
      | Some E', Some P' => Some (TEPi E' P') | _, _ => None end
  | TSwitch E P p e =>
      match lower k E, lower k P, lower k p, lower k e with
      | Some E', Some P', Some p', Some e' => Some (TSwitch E' P' p' e')
      | _, _, _, _ => None end
  | TIDesc IT => option_map TIDesc (lower k IT)
  | TIVar i => option_map TIVar (lower k i)
  | TI1 => Some TI1
  | TIProd A B =>
      match lower k A, lower k B with
      | Some A', Some B' => Some (TIProd A' B') | _, _ => None end
  | TIPi Sd T =>
      match lower k Sd, lower k T with
      | Some Sd', Some T' => Some (TIPi Sd' T') | _, _ => None end
  | TISig Sd T =>
      match lower k Sd, lower k T with
      | Some Sd', Some T' => Some (TISig Sd' T') | _, _ => None end
  | TIChoice E T =>
      match lower k E, lower k T with
      | Some E', Some T' => Some (TIChoice E' T') | _, _ => None end
  | TInterp D X =>
      match lower k D, lower k X with
      | Some D', Some X' => Some (TInterp D' X') | _, _ => None end
  | TMuI R => option_map TMuI (lower k R)
  | TMuS Sf => option_map TMuS (lower k Sf)
  | TIn x => option_map TIn (lower k x)
  | TInd R P s i x =>
      match lower k R, lower k P, lower k s, lower k i, lower k x with
      | Some R', Some P', Some s', Some i', Some x' =>
          Some (TInd R' P' s' i' x')
      | _, _, _, _, _ => None end
  | TIAll D X xs P =>
      match lower k D, lower k X, lower k xs, lower k P with
      | Some D', Some X', Some xs', Some P' => Some (TIAll D' X' xs' P')
      | _, _, _, _ => None end
  | THyps D X P h xs =>
      match lower k D, lower k X, lower k P, lower k h, lower k xs with
      | Some D', Some X', Some P', Some h', Some xs' =>
          Some (THyps D' X' P' h' xs')
      | _, _, _, _, _ => None end
  | TList A => option_map TList (lower k A)
  | TLNil A => option_map TLNil (lower k A)
  | TLCons A a l =>
      match lower k A, lower k a, lower k l with
      | Some A', Some a', Some l' => Some (TLCons A' a' l') | _, _, _ => None end
  | TCase M Q bs =>
      match lower k M, lower k Q, lower_bs lower k bs with
      | Some M', Some Q', Some bs' => Some (TCase M' Q' bs')
      | _, _, _ => None end
  end.

Lemma lower_var_lift : forall k n,
    lower k (lift 1 k (TVar n)) = Some (TVar n).
Proof.
  intros k n.
  cbv [lift].
  cbv [lower].
  destruct (Nat.ltb n k) eqn:Hlt.
  - rewrite Hlt. reflexivity.
  - idtac.
    assert (Hge : k <= n) by (apply Nat.ltb_ge; exact Hlt).
    assert (Hlt' : (1 + n) <? k = false) by
      (apply Nat.ltb_ge; lia).
    assert (Heq : (1 + n =? k) = false) by
      (apply Nat.eqb_neq; lia).
    rewrite Hlt', Heq.
    f_equal.
Qed.

Lemma lower_bs_lift_bound : forall N,
    (forall u, tsize u < N -> forall k,
       lower k (lift 1 k u) = Some u) ->
    forall k bs,
      bsize bs < N ->
      lower_bs lower k
        (map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) bs) = Some bs.
Proof.
  intros N H.
  intros k bs. revert k.
  induction bs as [|[c b] bs IH]; intros k Hbs.
  - reflexivity.
  - cbn [bsize] in Hbs.
    cbn [map].
    cbn [lower_bs].
    assert (Hc : tsize c < N) by
      (pose proof (tsize_pos b); lia).
    assert (Hb : tsize b < N) by
      (pose proof (tsize_pos c); lia).
    assert (Htail : bsize bs < N) by lia.
    rewrite (H c Hc k), (H b Hb (S k)), (IH k Htail).
    reflexivity.
Qed.

Ltac lower_rewrite_ih :=
  let H := match goal with
  | H0 : forall u : term, tsize u < tsize ?tt ->
      forall kk : nat, lower kk (lift 1 kk u) = Some u |- _ =>
      constr:(H0)
  end in
  repeat match goal with
  | |- context [lower ?kk (lift 1 ?kk ?uu)] =>
      rewrite (H ?uu ltac:(cbn; lia) ?kk)
  end.

Lemma lower_lift_aux : forall t k,
    lower k (lift 1 k t) = Some t.
Proof.
  apply (tsize_strong_ind
    (fun t => forall k, lower k (lift 1 k t) = Some t)).
  intros t IH k.
  destruct t; cbn [lift].
  all: try solve [cbv [lower]; eauto using lower_var_lift].
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) (S k)); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) (S k)); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) (S k)); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k), (IH t3 ltac:(cbn; lia) k),
      (IH t4 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k), (IH t3 ltac:(cbn; lia) k),
      (IH t4 ltac:(cbn; lia) k), (IH t5 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k), (IH t3 ltac:(cbn; lia) k),
      (IH t4 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k), (IH t3 ltac:(cbn; lia) k),
      (IH t4 ltac:(cbn; lia) k), (IH t5 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k), (IH t3 ltac:(cbn; lia) k); reflexivity.
  - simpl lower. rewrite (IH t1 ltac:(cbn; lia) k),
      (IH t2 ltac:(cbn; lia) k).
    assert (Hb : bsize bs < tsize (TCase t1 t2 bs)) by
      (cbn; pose proof (tsize_pos t1); pose proof (tsize_pos t2); lia).
    rewrite (lower_bs_lift_bound (tsize (TCase t1 t2 bs))
      (fun u Hu kk => IH u Hu kk) k bs Hb).
    reflexivity.
Qed.

Lemma lower_lift : forall k t,
    lower k (lift 1 k t) = Some t.
Proof. intros k t; apply lower_lift_aux. Qed.

Lemma lower_bs_sound_bound : forall N,
    (forall u, tsize u < N -> forall k v,
       lower k u = Some v -> lift 1 k v = u) ->
    forall k bs bs',
      bsize bs < N ->
      lower_bs lower k bs = Some bs' ->
      map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) bs' = bs.
Proof.
  intros N H.
  intros k bs. revert k.
  induction bs as [|[c b] bs IH]; intros k bs' Hsize Hlow.
  - cbn [lower_bs] in Hlow. inversion Hlow. reflexivity.
  - cbn [bsize] in Hsize.
    cbn [lower_bs] in Hlow.
    destruct (lower k c) eqn:Hc; try discriminate.
    destruct (lower (S k) b) eqn:Hb; try discriminate.
    destruct (lower_bs lower k bs) eqn:Htail; try discriminate.
    inversion Hlow; subst bs'.
    cbn [map].
    f_equal.
    + f_equal.
      * exact (H c ltac:(pose proof (tsize_pos b); lia) k t Hc).
      * exact (H b ltac:(pose proof (tsize_pos c); lia)
          (S k) t0 Hb).
    + apply IH; [lia|exact Htail].
Qed.


End _tmp_lower.

(* Checked conversion metatheory: _tmp_eta_shape *)
Module _tmp_eta_shape.
Import _tmp_lower.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma lower_lift_succ_var : forall n k,
    lower k (lift 1 (S k) (TVar n)) =
    option_map (lift 1 k) (lower k (TVar n)).
Proof.
  intros n k.
  destruct (Nat.lt_trichotomy n k) as [Hlt|[Heq|Hgt]].
  - assert (Hnk : n <? k = true) by (apply Nat.ltb_lt; lia).
    assert (Hnsk : n <? S k = true) by (apply Nat.ltb_lt; lia).
    cbv [lift lower]. rewrite Hnsk. repeat rewrite Hnk.
    cbn [option_map lift]. rewrite Hnk. reflexivity.
  - subst n.
    assert (Hksk : k <? S k = true) by (apply Nat.ltb_lt; lia).
    assert (Hkk : k <? k = false) by (apply Nat.ltb_ge; lia).
    assert (Hkeq : k =? k = true) by (apply Nat.eqb_eq; reflexivity).
    cbv [lift lower]. rewrite Hksk. rewrite Hkk, Hkeq.
    cbn [option_map]. reflexivity.
  - assert (Hnsk : n <? S k = false) by (apply Nat.ltb_ge; lia).
    assert (Hsnk : 1+n <? k = false) by (apply Nat.ltb_ge; lia).
    assert (Hsneq : 1+n =? k = false) by (apply Nat.eqb_neq; lia).
    assert (Hnk : n <? k = false) by (apply Nat.ltb_ge; lia).
    assert (Hneq : n =? k = false) by (apply Nat.eqb_neq; lia).
    assert (Hpred : Nat.pred n <? k = false) by
      (apply Nat.ltb_ge; destruct n; cbn in *; lia).
    cbv [lift lower].
    rewrite Hnsk, Hsnk, Hsneq, Hnk, Hneq.
    cbn [option_map lift]. rewrite Hpred.
    f_equal. destruct n; [lia | reflexivity].
Qed.

Lemma lower_lift_succ_bs_bound : forall N,
    (forall u, tsize u < N -> forall k,
      lower k (lift 1 (S k) u) =
      option_map (lift 1 k) (lower k u)) ->
    forall k bs, bsize bs < N ->
      lower_bs lower k
        (map (fun '(c,b) => (lift 1 (S k) c, lift 1 (S (S k)) b)) bs) =
      option_map
        (map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)))
        (lower_bs lower k bs).
Proof.
  intros N H k bs. revert k.
  induction bs as [|[c b] bs IH]; intros k Hsize; cbn; [reflexivity |].
  assert (Hc : tsize c < N) by
    (pose proof (tsize_pos b); cbn in Hsize; lia).
  assert (Hb : tsize b < N) by
    (pose proof (tsize_pos c); cbn in Hsize; lia).
  rewrite (H c Hc k), (H b Hb (S k)), (IH k ltac:(cbn in Hsize; lia)).
  destruct (lower k c); destruct (lower (S k) b);
    destruct (lower_bs lower k bs); reflexivity.
Qed.

Lemma lower_lift_succ : forall t k,
    lower k (lift 1 (S k) t) =
    option_map (lift 1 k) (lower k t).
Proof.
  apply (tsize_strong_ind (fun t => forall k,
    lower k (lift 1 (S k) t) = option_map (lift 1 k) (lower k t))).
  intros t IH k. destruct t; cbn [lift lower].
  all: try solve [apply lower_lift_succ_var].
  all: try reflexivity.
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    repeat match goal with
    | |- context [lower ?q ?u] => destruct (lower q u)
    end;
    reflexivity].
  rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) k).
  rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) k).
  rewrite (lower_lift_succ_bs_bound (tsize (TCase t1 t2 bs))
    (fun u Hu q => IH u Hu q) k bs ltac:(cbn; lia)).
  destruct (lower k t1); destruct (lower k t2);
    destruct (lower_bs lower k bs); reflexivity.
Qed.

Lemma lift_eta_shape_decomp : forall f h,
    lift 1 0 f = TLam (TApp (lift 1 0 h) (TVar 0)) ->
    exists u, h = lift 1 0 u.
Proof.
  intros f h Heq. destruct f; cbn [lift] in Heq; try discriminate.
  inversion Heq; subst.
  destruct f; cbn [lift] in H0; try discriminate.
  - destruct (Nat.ltb n 1); discriminate.
  - inversion H0; subst.
    match goal with
    | Hfg : lift 1 1 ?g = lift 1 0 h |- _ =>
        pose proof (f_equal (lower 0) Hfg) as Hlow
    end.
    rewrite lower_lift, lower_lift_succ in Hlow.
    destruct (lower 0 f1) as [u|] eqn:Hf; cbn in Hlow; try discriminate.
    inversion Hlow; subst. exists u. reflexivity.
Qed.

Lemma lower_lift_gap_var : forall n q r,
    lower q (lift 1 (S (q + r)) (TVar n)) =
    option_map (lift 1 (q + r)) (lower q (TVar n)).
Proof.
  intros n q r.
  destruct (Nat.lt_trichotomy n q) as [Hlt|[Heq|Hgt]].
  - assert (Hsrc : n <? S (q + r) = true) by
      (apply Nat.ltb_lt; lia).
    assert (Hq : n <? q = true) by (apply Nat.ltb_lt; lia).
    assert (Hout : n <? q + r = true) by (apply Nat.ltb_lt; lia).
    cbv [lift lower]. rewrite Hsrc, Hq.
    cbn [option_map lift]. rewrite Hout. reflexivity.
  - subst n.
    assert (Hsrc : q <? S (q + r) = true) by
      (apply Nat.ltb_lt; lia).
    assert (Hlt : q <? q = false) by (apply Nat.ltb_ge; lia).
    assert (Heq : q =? q = true) by (apply Nat.eqb_eq; reflexivity).
    cbv [lift lower]. rewrite Hsrc, Hlt, Heq. reflexivity.
  - assert (Hq : n <? q = false) by (apply Nat.ltb_ge; lia).
    assert (Hneq : n =? q = false) by (apply Nat.eqb_neq; lia).
    destruct (n <? S (q + r)) eqn:Hsrc.
    + assert (Hout : Nat.pred n <? q + r = true).
      { apply Nat.ltb_lt. apply Nat.ltb_lt in Hsrc.
        destruct n; cbn in *; lia. }
      cbv [lift lower]. rewrite Hsrc, Hq, Hneq.
      cbn [option_map lift]. rewrite Hout. reflexivity.
    + assert (Hsrcq : 1 + n <? q = false) by
        (apply Nat.ltb_ge; lia).
      assert (Hsrceq : 1 + n =? q = false) by
        (apply Nat.eqb_neq; lia).
      assert (Hout : Nat.pred n <? q + r = false).
      { apply Nat.ltb_ge. apply Nat.ltb_ge in Hsrc.
        destruct n; cbn in *; lia. }
      cbv [lift lower]. rewrite Hsrc, Hsrcq, Hsrceq, Hq, Hneq.
      cbn [option_map lift]. rewrite Hout.
      destruct n; [lia | reflexivity].
Qed.

Lemma lower_lift_gap_bs_bound : forall N,
    (forall u, tsize u < N -> forall q r,
      lower q (lift 1 (S (q + r)) u) =
      option_map (lift 1 (q + r)) (lower q u)) ->
    forall q r bs, bsize bs < N ->
      lower_bs lower q
        (map (fun '(c,b) =>
          (lift 1 (S (q + r)) c,
           lift 1 (S (S (q + r))) b)) bs) =
      option_map
        (map (fun '(c,b) =>
          (lift 1 (q + r) c, lift 1 (S (q + r)) b)))
        (lower_bs lower q bs).
Proof.
  intros N H q r bs. revert q r.
  induction bs as [|[c b] bs IH]; intros q r Hsize; cbn; [reflexivity |].
  assert (Hc : tsize c < N) by
    (pose proof (tsize_pos b); cbn in Hsize; lia).
  assert (Hb : tsize b < N) by
    (pose proof (tsize_pos c); cbn in Hsize; lia).
  rewrite (H c Hc q r).
  pose proof (H b Hb (S q) r) as Hbody.
  replace (S q + r) with (S (q + r)) in Hbody by lia.
  rewrite Hbody, (IH q r ltac:(cbn in Hsize; lia)).
  destruct (lower q c); destruct (lower (S q) b);
    destruct (lower_bs lower q bs); reflexivity.
Qed.

Lemma lower_lift_gap : forall t q r,
    lower q (lift 1 (S (q + r)) t) =
    option_map (lift 1 (q + r)) (lower q t).
Proof.
  apply (tsize_strong_ind (fun t => forall q r,
    lower q (lift 1 (S (q + r)) t) =
    option_map (lift 1 (q + r)) (lower q t))).
  intros t IH q r. destruct t; cbn [lift lower].
  all: try solve [apply lower_lift_gap_var].
  all: try reflexivity.
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    repeat match goal with
    | |- context [lower ?qq ?u] => destruct (lower qq u)
    end;
    reflexivity].
  - rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) q r).
    pose proof (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia)
      (S q) r) as Hbody.
    replace (S q + r) with (S (q + r)) in Hbody by lia.
    rewrite Hbody.
    destruct (lower q t1); destruct (lower (S q) t2); reflexivity.
  - pose proof (IH t ltac:(cbn; lia) (S q) r) as Hbody.
    replace (S q + r) with (S (q + r)) in Hbody by lia.
    rewrite Hbody. destruct (lower (S q) t); reflexivity.
  - rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) q r).
    pose proof (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia)
      (S q) r) as Hbody.
    replace (S q + r) with (S (q + r)) in Hbody by lia.
    rewrite Hbody.
    destruct (lower q t1); destruct (lower (S q) t2); reflexivity.
  - rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) q r).
    rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) q r).
    rewrite (lower_lift_gap_bs_bound (tsize (TCase t1 t2 bs))
      (fun u Hu qq rr => IH u Hu qq rr) q r bs ltac:(cbn; lia)).
    destruct (lower q t1); destruct (lower q t2);
      destruct (lower_bs lower q bs); reflexivity.
Qed.

Lemma lift_one_injective : forall k x y,
    lift 1 k x = lift 1 k y -> x = y.
Proof.
  intros k x y Heq.
  pose proof (f_equal (lower k) Heq) as Hlow.
  repeat rewrite lower_lift in Hlow. now inversion Hlow.
Qed.

Lemma lift_eta_shape_decomp_k : forall f h k,
    lift 1 k f = TLam (TApp (lift 1 0 h) (TVar 0)) ->
    exists u,
      h = lift 1 k u /\
      f = TLam (TApp (lift 1 0 u) (TVar 0)).
Proof.
  intros f h k Heq.
  destruct f; cbn [lift] in Heq; try discriminate.
  - destruct (Nat.ltb n k); discriminate.
  - inversion Heq; subst.
    destruct f; cbn [lift] in H0; try discriminate.
    + destruct (Nat.ltb n (S k)); discriminate.
    + inversion H0; subst.
      assert (Harg' : lift 1 (S k) f2 = lift 1 (S k) (TVar 0))
        by (rewrite H2; reflexivity).
      apply lift_one_injective in Harg'. subst f2.
      pose proof (f_equal (lower 0) H1) as Hlow.
      rewrite lower_lift in Hlow.
      replace (S k) with (S (0 + k)) in Hlow by lia.
      rewrite lower_lift_gap in Hlow.
      destruct (lower 0 f1) as [u|] eqn:Hlower; cbn in Hlow;
        try discriminate.
      inversion Hlow; subst h.
      exists u. split; [reflexivity |].
      rewrite H2. f_equal. f_equal.
      apply lift_one_injective with (k := S k).
      rewrite lift_lift_one_zero. assumption.
Qed.

End _tmp_eta_shape.

(* Checked conversion metatheory: _tmp_epstep_inv *)
Module _tmp_epstep_inv.
Import _tmp_epstep _tmp_eta_shape.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma tsize_lift_inv_local : forall t d k, tsize (lift d k t) = tsize t.
Proof.
  assert (Hmap : forall bs d k,
      (forall c b, In (c,b) bs ->
        tsize (lift d k c) = tsize c /\
        tsize (lift d (S k) b) = tsize b) ->
      bsize (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs) =
      bsize bs).
  {
    intros bs d k H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    rewrite (proj1 (H c b (or_introl eq_refl))).
    rewrite (proj2 (H c b (or_introl eq_refl))).
    rewrite (IH ltac:(intros c' b' Hin; apply H; right; exact Hin)).
    reflexivity.
  }
  apply (tsize_strong_ind (fun t => forall d k,
    tsize (lift d k t) = tsize t)).
  intros t IH d k. destruct t; cbn [lift tsize].
  all: try solve [destruct (Nat.ltb n k); reflexivity].
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    reflexivity].
  rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) d k).
  rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) d k).
  rewrite (Hmap bs d k ltac:(intros c b Hin; split;
    [apply IH; eapply tsize_case_bs; exact Hin |
     apply IH; eapply tsize_case_bs_body; exact Hin])).
  reflexivity.
Qed.

Lemma epbranches_lift_inv_bound : forall N,
    (forall f, tsize f < N -> forall k T,
      epstep (lift 1 k f) T ->
      exists u, T = lift 1 k u /\ epstep f u) ->
    forall bs k BS, bsize bs < N ->
      epbranches
        (map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) bs) BS ->
      exists us,
        BS = map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) us /\
        epbranches bs us.
Proof.
  intros N H bs. induction bs as [|[c b] bs IHbs];
    intros k BS Hsize Hep; cbn in Hep.
  - inversion Hep; subst. exists []; split; constructor.
  - inversion Hep; subst.
    match goal with
    | Hc : epstep (lift 1 k c) ?c' ,
      Hb : epstep (lift 1 (S k) b) ?b',
      Hbs : epbranches
        (map (fun '(c0,b0) =>
          (lift 1 k c0, lift 1 (S k) b0)) bs) ?bs' |- _ =>
      destruct (H c ltac:(pose proof (tsize_pos b); cbn in Hsize; lia)
        k c' Hc) as [u [Hu Hcu]];
      destruct (H b ltac:(pose proof (tsize_pos c); cbn in Hsize; lia)
        (S k) b' Hb) as [v [Hv Hbv]];
      destruct (IHbs k bs' ltac:(cbn in Hsize; lia) Hbs)
        as [us [Hus Hbus]]
    end.
    subst. exists ((u,v)::us). split; [reflexivity |].
    constructor; assumption.
Qed.

Ltac ep_inv_child IH :=
  match goal with
  | Hs : epstep (lift 1 ?q ?x) ?y |- _ =>
      let u := fresh "u" in
      let He := fresh "Heq" in
      let Hp := fresh "Hep" in
      destruct (IH x ltac:(cbn; lia) q y Hs) as [u [He Hp]];
      subst y
  end.

Lemma epstep_lift_inv : forall f k T,
    epstep (lift 1 k f) T ->
    exists u, T = lift 1 k u /\ epstep f u.
Proof.
  apply (tsize_strong_ind (fun f => forall k T,
    epstep (lift 1 k f) T ->
    exists u, T = lift 1 k u /\ epstep f u)).
  intros f IH k T Hstep.
  destruct f; cbn [lift] in Hstep.
  - destruct (Nat.ltb n k) eqn:Hlt; inversion Hstep; subst.
    + exists (TVar n). split;
        [cbn [lift]; rewrite Hlt; reflexivity | exact (eps_var n)].
    + exists (TVar n). split;
        [cbn [lift]; rewrite Hlt; reflexivity | exact (eps_var n)].
  - inversion Hstep; subst. exists (TSort k0); split; constructor.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TPi A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst.
    + ep_inv_child IH. exists (TLam u). split; [reflexivity | constructor; assumption].
    + assert (Hshapeeq :
          lift 1 k (TLam f) = TLam (TApp (lift 1 0 f0) (TVar 0))) by
        (cbn [lift]; f_equal; symmetry; assumption).
      pose proof (lift_eta_shape_decomp_k (TLam f) f0 k Hshapeeq) as Hshape.
      destruct Hshape as [u [Hfu Hsource]].
      subst f0.
      assert (Husize : tsize u < tsize (TLam f)).
      { pose proof (tsize_lift_inv_local u 1 0) as Hlift_size.
        rewrite Hsource. cbn [tsize]. lia. }
      destruct (IH u Husize k T H0)
        as [v [Hv Huv]].
      subst T. exists v. split; [reflexivity |].
      rewrite Hsource. constructor. assumption.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TApp A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TSigma A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TPair A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TFst u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TSnd u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. exists TUnitT; split; constructor.
  - inversion Hstep; subst. exists TUnit; split; constructor.
  - inversion Hstep; subst. exists TUId; split; constructor.
  - inversion Hstep; subst. exists (TTag s); split; constructor.
  - inversion Hstep; subst. exists TEnumU; split; constructor.
  - inversion Hstep; subst. exists TNilE; split; constructor.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TConsE A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TEnumT u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. exists TEZero; split; constructor.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TESucc u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TEPi A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?A, H2 : epstep f2 ?B,
      H3 : epstep f3 ?p, H4 : epstep f4 ?e |- _ =>
      exists (TSwitch A B p e); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TIDesc u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TIVar u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. exists TI1; split; constructor.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TIProd A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TIPi A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TISig A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TIChoice A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TInterp A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TMuI u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TMuS u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TIn u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?a1, H2 : epstep f2 ?a2,
      H3 : epstep f3 ?a3, H4 : epstep f4 ?a4,
      H5 : epstep f5 ?a5 |- _ =>
      exists (TInd a1 a2 a3 a4 a5); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?a1, H2 : epstep f2 ?a2,
      H3 : epstep f3 ?a3, H4 : epstep f4 ?a4 |- _ =>
      exists (TIAll a1 a2 a3 a4); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?a1, H2 : epstep f2 ?a2,
      H3 : epstep f3 ?a3, H4 : epstep f4 ?a4,
      H5 : epstep f5 ?a5 |- _ =>
      exists (THyps a1 a2 a3 a4 a5); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TList u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TLNil u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?a1, H2 : epstep f2 ?a2,
      H3 : epstep f3 ?a3 |- _ =>
      exists (TLCons a1 a2 a3); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | Hbs : epbranches
        (map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) bs) ?BS |- _ =>
      destruct (epbranches_lift_inv_bound (tsize (TCase f1 f2 bs))
        (fun x Hx q Y HY => IH x Hx q Y HY)
        bs k BS ltac:(cbn; lia) Hbs) as [us [Hus Heps]]
    end.
    subst.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TCase A B us); split;
        [reflexivity | constructor; assumption]
    end.
Qed.

End _tmp_epstep_inv.

(* Checked conversion metatheory: _tmp_eta_tool *)
Module _tmp_eta_tool.
Import _tmp_epstep _tmp_epstep_inv.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma eta_app_inv : forall f t,
  epstep (TApp (lift 1 0 f) (TVar 0)) t ->
  exists u, t = TApp (lift 1 0 u) (TVar 0) /\ epstep f u.
Proof.
  intros f t H.
  inversion H; subst.
  inversion H4; subst a'.
  destruct (epstep_lift_inv f 0 f' H2) as [u [Hu Hfu]].
  exists u. split; [rewrite Hu; reflexivity | exact Hfu].
Qed.

End _tmp_eta_tool.

(* Checked conversion metatheory: _tmp_epstep_diamond *)
Module _tmp_epstep_diamond.
Import _tmp_epstep _tmp_eta_shape _tmp_epstep_inv _tmp_eta_tool.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Ltac take_join :=
  match goal with
  | IH : forall z, epstep ?s z ->
        exists w, epstep ?t w /\ epstep z w,
    H : epstep ?s ?z |- _ =>
      first [ constr_eq z t; fail 1
            | let w := fresh "w" in
              let Hl := fresh "Hleft" in
              let Hr := fresh "Hright" in
              destruct (IH z H) as [w [Hl Hr]];
              clear IH ]
  | IH : forall zs, epbranches ?ss zs ->
        exists ws, epbranches ?ts ws /\ epbranches zs ws,
    H : epbranches ?ss ?zs |- _ =>
      first [ constr_eq zs ts; fail 1
            | let ws := fresh "ws" in
              let Hl := fresh "Hleft" in
              let Hr := fresh "Hright" in
              destruct (IH zs H) as [ws [Hl Hr]];
              clear IH ]
  end.

Ltac invert_other :=
  match goal with
  | Hother : epstep ?s ?u
      |- exists v, epstep ?t v /\ epstep ?u v =>
      inversion Hother; subst; clear Hother
  | Hother : epbranches ?ss ?us
      |- exists vs, epbranches ?ts vs /\ epbranches ?us vs =>
      inversion Hother; subst; clear Hother
  end.

Lemma epstep_diamond_mut :
  (forall s t (H : epstep s t), forall u, epstep s u ->
      exists v, epstep t v /\ epstep u v) /\
  (forall ss ts (H : epbranches ss ts), forall us, epbranches ss us ->
      exists vs, epbranches ts vs /\ epbranches us vs).
Proof.
  apply epstep_epbranches_ind.
  all: intros.
  all: invert_other.
  all: repeat take_join.
  all: try solve [eexists; split; econstructor; eassumption].
  - match goal with
    | IH : forall z, epstep (TApp (lift 1 0 ?f) (TVar 0)) z -> _,
      E : epstep (TApp (lift 1 0 f) (TVar 0)) ?b',
      Hfu : epstep f ?u |- _ =>
      destruct (eta_app_inv f b' E) as [g [Hbg Hfg]];
      subst b';
      assert (Hbodyu : epstep
        (TApp (lift 1 0 f) (TVar 0))
        (TApp (lift 1 0 u) (TVar 0))) by
        (constructor; [apply epstep_lift; exact Hfu | constructor]);
      destruct (IH _ Hbodyu) as [v [Hgv Huv]];
      destruct (eta_app_inv g v Hgv) as [x [Hvx Hgx]];
      destruct (eta_app_inv u v Huv) as [y [Hvy Huy]]
    end.
    assert (Hxy : x = y).
    { rewrite Hvx in Hvy. inversion Hvy.
      apply lift_one_injective with (k := 0). assumption. }
    subst y. exists x. split.
    + apply eps_eta. exact Hgx.
    + exact Huy.
  - match goal with
    | IH : forall z, epstep ?f z -> _,
      Hb : epstep (TApp (lift 1 0 f) (TVar 0)) ?b' |- _ =>
      destruct (eta_app_inv f b' Hb) as [g [Hbg Hfg]];
      subst b';
      destruct (IH g Hfg) as [w [Hfw Hgw]];
      exists w; split; [exact Hfw | apply eps_eta; exact Hgw]
    end.
  - apply lift_one_injective in H1. subst f0.
    exact (H u H2).
Qed.

Corollary epstep_diamond : forall s t u,
    epstep s t -> epstep s u ->
    exists v, epstep t v /\ epstep u v.
Proof.
  intros s t u Hst Hsu.
  exact (proj1 epstep_diamond_mut s t Hst u Hsu).
Qed.

Corollary epbranches_diamond : forall ss ts us,
    epbranches ss ts -> epbranches ss us ->
    exists vs, epbranches ts vs /\ epbranches us vs.
Proof.
  intros ss ts us Hst Hsu.
  exact (proj2 epstep_diamond_mut ss ts Hst us Hsu).
Qed.

End _tmp_epstep_diamond.

(* Checked conversion metatheory: _tmp_epstep_subst *)
Module _tmp_epstep_subst.
Import _tmp_epstep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma epstep_subst_mut :
  (forall t t' (H : epstep t t'), forall u u' k,
      epstep u u' -> epstep (subst u k t) (subst u' k t')) /\
  (forall bs bs' (H : epbranches bs bs'), forall u u' k,
      epstep u u' ->
      epbranches
        (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
        (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) bs')).
Proof.
  apply epstep_epbranches_ind; cbn; intros;
    try solve [constructor; eauto using epstep_refl, epstep_lift].
  - change (epstep (subst u k (TVar n)) (subst u' k (TVar n))).
    destruct (Nat.lt_trichotomy n k) as [Hnk | [Hnk | Hnk]].
    + assert (Hlt : Nat.ltb n k = true) by (apply Nat.ltb_lt; lia).
      cbn [subst]. rewrite Hlt. apply epstep_refl.
    + subst n.
      assert (Hlt : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
      cbn [subst]. rewrite Hlt, Heq. eapply epstep_lift. exact H.
    + assert (Hlt : Nat.ltb n k = false) by (apply Nat.ltb_ge; lia).
      assert (Heq : Nat.eqb n k = false) by (apply Nat.eqb_neq; lia).
      cbn [subst]. rewrite Hlt, Heq. apply epstep_refl.
  - rewrite subst_lift_one_zero.
    eapply eps_eta. eauto.
Qed.

Corollary epstep_subst : forall t t', epstep t t' -> forall u u' k,
    epstep u u' -> epstep (subst u k t) (subst u' k t').
Proof. intros t t' H. exact (proj1 epstep_subst_mut t t' H). Qed.

Corollary epbranches_subst : forall bs bs', epbranches bs bs' ->
    forall u u' k, epstep u u' ->
    epbranches
      (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs)
      (map (fun '(c,b) => (subst u' k c, subst u' (S k) b)) bs').
Proof. intros bs bs' H. exact (proj2 epstep_subst_mut bs bs' H). Qed.

End _tmp_epstep_subst.

(* Checked conversion metatheory: _luna_enum_pos_lift_inv *)
Module _luna_enum_pos_lift_inv.

Import TypeRulesCore.

Lemma enum_pos_lift_inv_luna : forall c n d k,
    enum_pos (lift d k c) n -> enum_pos c n.
Proof.
  intros c n d k. revert n.
  induction c; intros n0 H; cbn [lift] in H;
    try solve [destruct (Nat.ltb _ _) eqn:Hl; cbn in H; inversion H];
    try inversion H.
  - inversion H; constructor.
  - inversion H; subst. constructor. apply IHc. assumption.
Qed.

End _luna_enum_pos_lift_inv.

(* Checked conversion metatheory: _work_pstep_lift_inv *)
Module _work_pstep_lift_inv.
Import _tmp_eta_shape _luna_enum_pos_lift_inv.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

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

End _work_pstep_lift_inv.

(* Checked conversion metatheory: _tmp_pstep_var_rigid *)
Module _tmp_pstep_var_rigid.

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma pstep_var_rigid : forall n t, pstep (TVar n) t -> t = TVar n.
Proof.
  intros n t H.
  inversion H; reflexivity.
Qed.

End _tmp_pstep_var_rigid.

(* Checked conversion metatheory: _tmp_eta_cancel *)
Module _tmp_eta_cancel.

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma subst_eta_beta_cancel_var : forall n k,
    subst (TVar 0) k (lift 1 (S k) (TVar n)) = TVar n.
Proof.
  intros n k. cbn [lift].
  destruct (Nat.ltb n (S k)) eqn:Hn.
  - apply Nat.ltb_lt in Hn. cbn [subst].
    destruct (Nat.eq_dec n k) as [->|Hneq].
    + rewrite Nat.ltb_irrefl, Nat.eqb_refl. cbn [lift].
      replace (k + 0) with k by lia. reflexivity.
    + assert (Hlt : Nat.ltb n k = true) by
        (apply Nat.ltb_lt; lia).
      rewrite Hlt. reflexivity.
  - apply Nat.ltb_ge in Hn. cbn [subst].
    assert (Hlt : Nat.ltb (1+n) k = false) by
      (apply Nat.ltb_ge; lia).
    assert (Heq : Nat.eqb (1+n) k = false) by
      (apply Nat.eqb_neq; lia).
    rewrite Hlt, Heq. f_equal.
Qed.

Lemma subst_eta_beta_cancel_gen : forall t k,
    subst (TVar 0) k (lift 1 (S k) t) = t.
Proof.
  apply (tsize_strong_ind (fun t => forall k,
    subst (TVar 0) k (lift 1 (S k) t) = t)).
  intros t IH k. destruct t; cbn [lift subst].
  all: try solve [apply subst_eta_beta_cancel_var].
  all: try reflexivity.
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    reflexivity].
  rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) k).
  rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) k).
  f_equal.
  induction bs as [|[c b] bs IHbs]; cbn; [reflexivity |].
  f_equal.
  f_equal.
  - apply IH. eapply tsize_case_bs. left. reflexivity.
  - apply IH. eapply tsize_case_bs_body. left. reflexivity.
  - apply IHbs. intros u Hu. apply IH. cbn in *. lia.
Qed.

Corollary subst_eta_beta_cancel : forall t,
    subst (TVar 0) 0 (lift 1 1 t) = t.
Proof. intros t. apply subst_eta_beta_cancel_gen. Qed.

End _tmp_eta_cancel.

(* Checked conversion metatheory: _work_eta_critical *)
Module _work_eta_critical.
Import _tmp_epstep _tmp_pstep_var_rigid _tmp_eta_cancel _work_pstep_lift_inv.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Definition eta_app (f : term) : term :=
  TApp (lift 1 0 f) (TVar 0).

Lemma pstep_eta_app_cases : forall f q,
    pstep (eta_app f) q ->
    (exists g, q = eta_app g /\ pstep f g) \/
    (exists b b', f = TLam b /\ q = b' /\ pstep b b').
Proof.
  intros f q H. unfold eta_app in H.
  inversion H; subst.
  - assert (Ha : a' = TVar 0) by (eapply pstep_var_rigid; eassumption).
    subst a'.
    destruct (pstep_lift_inv f 0 f' H2) as [g [Hg Hfg]].
    subst f'. left. exists g. split; [reflexivity | exact Hfg].
  - destruct f; cbn [lift] in H0; try discriminate.
    inversion H0; subst b; clear H0.
    assert (Ha : a' = TVar 0) by (eapply pstep_var_rigid; eassumption).
    subst a'.
    destruct (pstep_lift_inv f 1 b' H2) as [bd [Hbd Hpbd]].
    subst b'. rewrite subst_eta_beta_cancel.
    right. exists f, bd. repeat split; assumption.
Qed.

Lemma rtc_epstep_lam : forall a b,
    rtc epstep a b -> rtc epstep (TLam a) (TLam b).
Proof.
  intros a b H. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply eps_lam; exact H | exact IHrtc].
Qed.

Lemma eta_lambda_critical_rtc : forall f u b',
    epstep f u ->
    (forall z, epstep (eta_app f) z ->
      exists q, rtc epstep b' q /\ pstep z q) ->
    exists v, rtc epstep (TLam b') v /\ pstep u v.
Proof.
  intros f u b' Hfu IH.
  assert (Hbody : epstep (eta_app f) (eta_app u)).
  { unfold eta_app. constructor.
    - eapply epstep_lift. exact Hfu.
    - constructor. }
  destruct (IH _ Hbody) as [q [Hbq Huq]].
  destruct (pstep_eta_app_cases u q Huq) as
    [[g [Hq Hug]] | [body [body' [Hu [Hq Hbodycore]]]]].
  - subst q. exists g. split; [|exact Hug].
    eapply rtc_trans.
    + apply rtc_epstep_lam. exact Hbq.
    + apply rtc_one. unfold eta_app. apply eps_eta, epstep_refl.
  - subst u q. exists (TLam body'). split.
    + apply rtc_epstep_lam. exact Hbq.
    + apply ps_lam. exact Hbodycore.
Qed.

End _work_eta_critical.

(* Checked conversion metatheory: _work_epstep_rtc *)
Module _work_epstep_rtc.
Import _tmp_epstep _tmp_epstep_subst.
From Stdlib Require Import List.
Import ListNotations TypeRulesCore.

Lemma rtc_map_rel : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> Y),
    (forall x y, R x y -> S (F x) (F y)) ->
    forall x y, rtc R x y -> rtc S (F x) (F y).
Proof.
  intros X Y R S F HF x y H. induction H.
  - apply rtc_refl.
  - eapply rtc_step; [apply HF; exact H | exact IHrtc].
Qed.

Lemma rtc_map_rel2 : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> X -> Y),
    (forall x y z, R x y -> S (F x z) (F y z)) ->
    (forall z x y, R x y -> S (F z x) (F z y)) ->
    forall a a' b b', rtc R a a' -> rtc R b b' ->
      rtc S (F a b) (F a' b').
Proof.
  intros X Y R S F H1 H2 a a' b b' Ha Hb. eapply rtc_trans.
  - eapply (rtc_map_rel X Y R S (fun x => F x b));
      [intros; apply H1; assumption | exact Ha].
  - eapply (rtc_map_rel X Y R S (fun x => F a' x));
      [intros; apply H2; assumption | exact Hb].
Qed.

Lemma rtc_map_rel3 : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> X -> X -> Y),
    (forall x y b c, R x y -> S (F x b c) (F y b c)) ->
    (forall a x y c, R x y -> S (F a x c) (F a y c)) ->
    (forall a b x y, R x y -> S (F a b x) (F a b y)) ->
    forall a a' b b' c c',
      rtc R a a' -> rtc R b b' -> rtc R c c' ->
      rtc S (F a b c) (F a' b' c').
Proof.
  intros X Y R S F H1 H2 H3 a a' b b' c c' Ha Hb Hc.
  eapply rtc_trans.
  - eapply (rtc_map_rel X Y R S (fun x => F x b c));
      [intros; apply H1; assumption | exact Ha].
  - eapply rtc_trans.
    + eapply (rtc_map_rel X Y R S (fun x => F a' x c));
        [intros; apply H2; assumption | exact Hb].
    + eapply (rtc_map_rel X Y R S (fun x => F a' b' x));
        [intros; apply H3; assumption | exact Hc].
Qed.

Lemma rtc_map_rel4 : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> X -> X -> X -> Y),
    (forall x y b c d, R x y -> S (F x b c d) (F y b c d)) ->
    (forall a x y c d, R x y -> S (F a x c d) (F a y c d)) ->
    (forall a b x y d, R x y -> S (F a b x d) (F a b y d)) ->
    (forall a b c x y, R x y -> S (F a b c x) (F a b c y)) ->
    forall a a' b b' c c' d d',
      rtc R a a' -> rtc R b b' -> rtc R c c' -> rtc R d d' ->
      rtc S (F a b c d) (F a' b' c' d').
Proof.
  intros X Y R S F H1 H2 H3 H4 a a' b b' c c' d d' Ha Hb Hc Hd.
  eapply rtc_trans.
  - eapply (rtc_map_rel X Y R S (fun x => F x b c d));
      [intros; apply H1; assumption | exact Ha].
  - eapply rtc_trans.
    + eapply (rtc_map_rel X Y R S (fun x => F a' x c d));
        [intros; apply H2; assumption | exact Hb].
    + eapply rtc_trans.
      * eapply (rtc_map_rel X Y R S (fun x => F a' b' x d));
          [intros; apply H3; assumption | exact Hc].
      * eapply (rtc_map_rel X Y R S (fun x => F a' b' c' x));
          [intros; apply H4; assumption | exact Hd].
Qed.

Lemma rtc_map_rel5 : forall X Y (R : X -> X -> Prop) (S : Y -> Y -> Prop)
    (F : X -> X -> X -> X -> X -> Y),
    (forall x y b c d e, R x y -> S (F x b c d e) (F y b c d e)) ->
    (forall a x y c d e, R x y -> S (F a x c d e) (F a y c d e)) ->
    (forall a b x y d e, R x y -> S (F a b x d e) (F a b y d e)) ->
    (forall a b c x y e, R x y -> S (F a b c x e) (F a b c y e)) ->
    (forall a b c d x y, R x y -> S (F a b c d x) (F a b c d y)) ->
    forall a a' b b' c c' d d' e e',
      rtc R a a' -> rtc R b b' -> rtc R c c' -> rtc R d d' ->
      rtc R e e' -> rtc S (F a b c d e) (F a' b' c' d' e').
Proof.
  intros X Y R S F H1 H2 H3 H4 H5
    a a' b b' c c' d d' e e' Ha Hb Hc Hd He.
  eapply rtc_trans.
  - eapply (rtc_map_rel X Y R S (fun x => F x b c d e));
      [intros; apply H1; assumption | exact Ha].
  - eapply rtc_trans.
    + eapply (rtc_map_rel X Y R S (fun x => F a' x c d e));
        [intros; apply H2; assumption | exact Hb].
    + eapply rtc_trans.
      * eapply (rtc_map_rel X Y R S (fun x => F a' b' x d e));
          [intros; apply H3; assumption | exact Hc].
      * eapply rtc_trans.
        -- eapply (rtc_map_rel X Y R S (fun x => F a' b' c' x e));
             [intros; apply H4; assumption | exact Hd].
        -- eapply (rtc_map_rel X Y R S (fun x => F a' b' c' d' x));
             [intros; apply H5; assumption | exact He].
Qed.

Lemma rtc_epstep_lift : forall t u,
    rtc epstep t u -> forall d k, rtc epstep (lift d k t) (lift d k u).
Proof.
  intros t u H d k. eapply rtc_map_rel; [|exact H].
  intros x y Hxy. eapply epstep_lift. exact Hxy.
Qed.

Lemma rtc_epstep_congr1 : forall (F : term -> term),
    (forall x y, epstep x y -> epstep (F x) (F y)) ->
    forall x y, rtc epstep x y -> rtc epstep (F x) (F y).
Proof. intros F HF x y H; eapply rtc_map_rel; eauto. Qed.

Lemma rtc_epstep_congr2 : forall (F : term -> term -> term),
    (forall a a' b b', epstep a a' -> epstep b b' ->
      epstep (F a b) (F a' b')) ->
    forall a a' b b', rtc epstep a a' -> rtc epstep b b' ->
      rtc epstep (F a b) (F a' b').
Proof.
  intros F HF a a' b b' Ha Hb.
  eapply rtc_map_rel2 with (F := F).
  - intros x y z Hxy. apply HF; [exact Hxy | apply epstep_refl].
  - intros z x y Hxy. apply HF; [apply epstep_refl | exact Hxy].
  - exact Ha.
  - exact Hb.
Qed.

Lemma rtc_epstep_congr3 : forall (F : term -> term -> term -> term),
    (forall a a' b b' c c',
      epstep a a' -> epstep b b' -> epstep c c' ->
      epstep (F a b c) (F a' b' c')) ->
    forall a a' b b' c c',
      rtc epstep a a' -> rtc epstep b b' -> rtc epstep c c' ->
      rtc epstep (F a b c) (F a' b' c').
Proof.
  intros F HF a a' b b' c c' Ha Hb Hc.
  eapply rtc_map_rel3 with (F := F).
  - intros x y z w Hxy. apply HF; eauto using epstep_refl.
  - intros z x y w Hxy. apply HF; eauto using epstep_refl.
  - intros z w x y Hxy. apply HF; eauto using epstep_refl.
  - exact Ha.
  - exact Hb.
  - exact Hc.
Qed.

Lemma rtc_epstep_congr4 : forall (F : term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d',
      epstep a a' -> epstep b b' -> epstep c c' -> epstep d d' ->
      epstep (F a b c d) (F a' b' c' d')) ->
    forall a a' b b' c c' d d',
      rtc epstep a a' -> rtc epstep b b' -> rtc epstep c c' ->
      rtc epstep d d' -> rtc epstep (F a b c d) (F a' b' c' d').
Proof.
  intros F HF a a' b b' c c' d d' Ha Hb Hc Hd.
  eapply rtc_map_rel4 with (F := F).
  - intros x y z w q Hxy. apply HF; eauto using epstep_refl.
  - intros z x y w q Hxy. apply HF; eauto using epstep_refl.
  - intros z w x y q Hxy. apply HF; eauto using epstep_refl.
  - intros z w q x y Hxy. apply HF; eauto using epstep_refl.
  - exact Ha.
  - exact Hb.
  - exact Hc.
  - exact Hd.
Qed.

Lemma rtc_epstep_congr5 :
    forall (F : term -> term -> term -> term -> term -> term),
    (forall a a' b b' c c' d d' e e',
      epstep a a' -> epstep b b' -> epstep c c' -> epstep d d' ->
      epstep e e' -> epstep (F a b c d e) (F a' b' c' d' e')) ->
    forall a a' b b' c c' d d' e e',
      rtc epstep a a' -> rtc epstep b b' -> rtc epstep c c' ->
      rtc epstep d d' -> rtc epstep e e' ->
      rtc epstep (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F HF a a' b b' c c' d d' e e' Ha Hb Hc Hd He.
  eapply rtc_map_rel5 with (F := F).
  - intros x y z w q r Hxy. apply HF; eauto using epstep_refl.
  - intros z x y w q r Hxy. apply HF; eauto using epstep_refl.
  - intros z w x y q r Hxy. apply HF; eauto using epstep_refl.
  - intros z w q x y r Hxy. apply HF; eauto using epstep_refl.
  - intros z w q r x y Hxy. apply HF; eauto using epstep_refl.
  - exact Ha.
  - exact Hb.
  - exact Hc.
  - exact Hd.
  - exact He.
Qed.

Lemma rtc_epstep_subst : forall t t' u u' k,
    rtc epstep t t' -> rtc epstep u u' ->
    rtc epstep (subst u k t) (subst u' k t').
Proof.
  intros t t' u u' k Ht Hu.
  eapply rtc_map_rel2 with (F := fun body arg => subst arg k body).
  - intros x y arg Hxy. eapply epstep_subst; [exact Hxy | apply epstep_refl].
  - intros body x y Hxy. eapply epstep_subst; [apply epstep_refl | exact Hxy].
  - exact Ht.
  - exact Hu.
Qed.

Lemma rtc_epbranches_cons : forall c c' b b' bs bs',
    rtc epstep c c' -> rtc epstep b b' -> rtc epbranches bs bs' ->
    rtc epbranches ((c,b)::bs) ((c',b')::bs').
Proof.
  intros c c' b b' bs bs' Hc Hb Hbs. eapply rtc_trans.
  - eapply rtc_map_rel with (F := fun x => (x,b)::bs); [|exact Hc].
    intros x y Hxy. constructor; [exact Hxy | apply epstep_refl | apply epbranches_refl].
  - eapply rtc_trans.
    + eapply rtc_map_rel with (F := fun x => (c',x)::bs); [|exact Hb].
      intros x y Hxy. constructor; [apply epstep_refl | exact Hxy | apply epbranches_refl].
    + eapply rtc_map_rel with (F := fun xs => (c',b')::xs); [|exact Hbs].
      intros xs ys Hxy. constructor; [apply epstep_refl | apply epstep_refl | exact Hxy].
Qed.

Lemma rtc_epstep_case : forall M M' Q Q' bs bs',
    rtc epstep M M' -> rtc epstep Q Q' -> rtc epbranches bs bs' ->
    rtc epstep (TCase M Q bs) (TCase M' Q' bs').
Proof.
  intros M M' Q Q' bs bs' HM HQ Hbs. eapply rtc_trans.
  - eapply rtc_map_rel with (F := fun x => TCase x Q bs); [|exact HM].
    intros x y Hxy. constructor; [exact Hxy | apply epstep_refl | apply epbranches_refl].
  - eapply rtc_trans.
    + eapply rtc_map_rel with (F := fun x => TCase M' x bs); [|exact HQ].
      intros x y Hxy. constructor; [apply epstep_refl | exact Hxy | apply epbranches_refl].
    + eapply rtc_map_rel with (F := fun xs => TCase M' Q' xs); [|exact Hbs].
      intros xs ys Hxy. constructor; [apply epstep_refl | apply epstep_refl | exact Hxy].
Qed.

End _work_epstep_rtc.

(* Checked conversion metatheory: _tmp_commute *)
Module _tmp_commute.
Import _tmp_epstep _tmp_eta_shape _tmp_epstep_inv _tmp_eta_tool _tmp_epstep_subst _work_pstep_lift_inv _work_eta_critical _work_epstep_rtc.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma lift_zero_id_local : forall t k, lift 0 k t = t.
Proof.
  assert (Hmap : forall bs k,
      (forall c b, In (c,b) bs ->
        lift 0 k c = c /\ lift 0 (S k) b = b) ->
      map (fun '(c,b) => (lift 0 k c, lift 0 (S k) b)) bs = bs).
  {
    intros bs k H. induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    rewrite (proj1 (H c b (or_introl eq_refl))).
    rewrite (proj2 (H c b (or_introl eq_refl))).
    rewrite (IH ltac:(intros c' b' Hin; apply H; right; exact Hin)).
    reflexivity.
  }
  apply (tsize_strong_ind (fun t => forall k, lift 0 k t = t)).
  intros t IH k. destruct t; cbn [lift].
  all: try solve [destruct (Nat.ltb n k); reflexivity].
  all: try reflexivity.
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    reflexivity].
  rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) k).
  rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) k).
  rewrite (Hmap bs k ltac:(intros c b Hin; split;
    [apply IH; eapply tsize_case_bs; exact Hin |
     apply IH; eapply tsize_case_bs_body; exact Hin])).
  reflexivity.
Qed.

Lemma subst_eta_app_local : forall f a,
    subst a 0 (TApp (lift 1 0 f) (TVar 0)) = TApp f a.
Proof.
  intros f a. cbn [subst].
  rewrite subst_lift_zero, lift_zero_id_local. reflexivity.
Qed.

Lemma epstep_enum_pos_id : forall c c' n,
    epstep c c' -> enum_pos c n -> c' = c.
Proof.
  intros c c' n Hep Hpos. revert c' Hep.
  induction Hpos; intros c' Hep; inversion Hep; subst; [reflexivity |].
  f_equal. eauto.
Qed.

Lemma epbranches_nth_error_fwd : forall bs bs' k c b,
    epbranches bs bs' -> nth_error bs k = Some (c,b) ->
    exists c' b', nth_error bs' k = Some (c',b') /\
      epstep c c' /\ epstep b b'.
Proof.
  intros bs bs' k c b Hbs. revert k c b.
  induction Hbs; intros k c0 b0 Hnth; destruct k; cbn in Hnth.
  - discriminate.
  - discriminate.
  - inversion Hnth; subst. eexists; eexists; repeat split; eauto.
  - eapply IHHbs; exact Hnth.
Qed.

Lemma epbranches_nth_error_rev : forall bs bs' k c' b',
    epbranches bs bs' -> nth_error bs' k = Some (c',b') ->
    exists c b, nth_error bs k = Some (c,b) /\
      epstep c c' /\ epstep b b'.
Proof.
  intros bs bs' k c' b' Hbs. revert k c' b'.
  induction Hbs; intros k c0 b0 Hnth; destruct k; cbn in Hnth.
  - discriminate.
  - discriminate.
  - inversion Hnth; subst. eexists; eexists; repeat split; eauto.
  - eapply IHHbs; exact Hnth.
Qed.

Ltac invert_eta_other :=
  match goal with
  | Hother : epstep ?s ?u
      |- exists v, rtc epstep ?t v /\ pstep ?u v =>
      inversion Hother; subst; clear Hother
  | Hother : epbranches ?ss ?us
      |- exists vs, rtc epbranches ?ts vs /\ pbranches ?us vs =>
      inversion Hother; subst; clear Hother
  end.

Ltac take_commute :=
  match goal with
  | IH : forall z, epstep ?s z ->
        exists w, rtc epstep ?t w /\ pstep z w,
    H : epstep ?s ?z |- _ =>
      let w := fresh "w" in
      let He := fresh "Heta" in
      let Hp := fresh "Hcore" in
      destruct (IH z H) as [w [He Hp]];
      clear IH
  | IH : forall zs, epbranches ?ss zs ->
        exists ws, rtc epbranches ?ts ws /\ pbranches zs ws,
    H : epbranches ?ss ?zs |- _ =>
      let ws := fresh "ws" in
      let He := fresh "Heta" in
      let Hp := fresh "Hcore" in
      destruct (IH zs H) as [ws [He Hp]];
      clear IH
  end.

Ltac invert_eta_known_shape :=
  match goal with
  | Hs : epstep (TLam _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TPair _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep TNilE _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep TEZero _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TESucc _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep TUnit _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TConsE _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIVar _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep TI1 _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIProd _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIPi _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TISig _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIChoice _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : epstep (TIn _) _ |- _ => inversion Hs; subst; clear Hs
  end.

Ltac eta_congruence :=
  first
    [ assumption
    | apply epstep_lift; eta_congruence
    | apply epstep_subst; eta_congruence
    | apply eps_var
    | apply eps_sort
    | apply eps_pi; eta_congruence
    | apply eps_lam; eta_congruence
    | apply eps_app; eta_congruence
    | apply eps_sigma; eta_congruence
    | apply eps_pair; eta_congruence
    | apply eps_fst; eta_congruence
    | apply eps_snd; eta_congruence
    | apply eps_unitt
    | apply eps_unit
    | apply eps_uid
    | apply eps_tag
    | apply eps_enumu
    | apply eps_nile
    | apply eps_conse; eta_congruence
    | apply eps_enumt; eta_congruence
    | apply eps_ezero
    | apply eps_esucc; eta_congruence
    | apply eps_epi; eta_congruence
    | apply eps_switch; eta_congruence
    | apply eps_idesc; eta_congruence
    | apply eps_ivar; eta_congruence
    | apply eps_i1
    | apply eps_iprod; eta_congruence
    | apply eps_ipi; eta_congruence
    | apply eps_isig; eta_congruence
    | apply eps_ichoice; eta_congruence
    | apply eps_interp; eta_congruence
    | apply eps_mui; eta_congruence
    | apply eps_mus; eta_congruence
    | apply eps_in; eta_congruence
    | apply eps_ind; eta_congruence
    | apply eps_iall; eta_congruence
    | apply eps_hyps; eta_congruence
    | apply eps_list; eta_congruence
    | apply eps_lnil; eta_congruence
    | apply eps_lcons; eta_congruence
    | apply eps_case; eta_congruence
    | apply epbs_nil
    | apply epbs_cons; eta_congruence ].

Ltac eta_rtc_congruence :=
  first
    [ assumption
    | apply rtc_refl
    | apply rtc_epstep_lift; eta_rtc_congruence
    | apply rtc_epstep_subst; eta_rtc_congruence
    | eapply rtc_epstep_congr1 with (F := fun x => TLam x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TFst x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TSnd x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TEnumT x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TESucc x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TIDesc x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TIVar x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TMuI x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TMuS x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TIn x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TList x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr1 with (F := fun x => TLNil x);
        [intros; eta_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TPi x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TApp x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TSigma x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TPair x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TConsE x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TEPi x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TIProd x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TIPi x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TISig x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TIChoice x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr2 with (F := fun x y => TInterp x y);
        [intros; eta_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr3 with (F := fun x y z => TLCons x y z);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr4 with (F := fun x y z w => TSwitch x y z w);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr4 with (F := fun x y z w => TIAll x y z w);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr5 with (F := fun x y z w q => TInd x y z w q);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence]
    | eapply rtc_epstep_congr5 with (F := fun x y z w q => THyps x y z w q);
        [intros; eta_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence |
         eta_rtc_congruence | eta_rtc_congruence]
    | apply rtc_epstep_case; eta_rtc_congruence
    | apply rtc_epbranches_cons; eta_rtc_congruence ].

Ltac apply_computation_root :=
  first
    [ eapply ps_fst_pair; eassumption
    | eapply ps_snd_pair; eassumption
    | eapply ps_epi_cons; eassumption
    | eapply ps_switch_zero; eassumption
    | eapply ps_switch_succ; eassumption
    | eapply ps_interp_prod; eassumption
    | eapply ps_interp_pi; eassumption
    | eapply ps_interp_sig; eassumption
    | eapply ps_interp_choice; eassumption
    | eapply ps_iall_var; eassumption
    | eapply ps_iall_prod; eassumption
    | eapply ps_iall_pi; eassumption
    | eapply ps_iall_sig; eassumption
    | eapply ps_iall_choice; eassumption
    | eapply ps_hyps_var; eassumption
    | eapply ps_hyps_prod; eassumption
    | eapply ps_hyps_pi; eassumption
    | eapply ps_hyps_sig; eassumption
    | eapply ps_hyps_choice; eassumption
    | eapply ps_ind_red; eassumption ].

Ltac solve_computation_root :=
  let v := fresh "common" in
  evar (v : term);
  exists v; split;
  cycle 2;
  [ apply_computation_root
  | subst v;
    eauto 30 using epstep_lift, epstep_subst, epstep_refl ].

Lemma pstep_epstep_commute_mut :
  (forall s t (H : pstep s t), forall u, epstep s u ->
      exists v, rtc epstep t v /\ pstep u v) /\
  (forall ss ts (H : pbranches ss ts), forall us, epbranches ss us ->
      exists vs, rtc epbranches ts vs /\ pbranches us vs).
Proof.
  apply pstep_pbranches_ind.
  all: intros.
  all: invert_eta_other.
  all: repeat invert_eta_known_shape.
  all: repeat take_commute.
  all: try solve [eexists; split; cycle 1;
    [econstructor; eauto using pstep_lift, pstep_subst, pstep_refl |
     eta_rtc_congruence]].
  all: try solve [eexists; split; cycle 1;
    [apply_core_root | eta_rtc_congruence]].
  all: try solve [eexists; split;
    [econstructor; eauto using epstep_lift, epstep_subst, epstep_refl |
     econstructor; eauto using pstep_lift, pstep_subst, pstep_refl]].
  all: try solve [
    match goal with
    | He : epstep ?x ?w |- exists v, epstep ?x v /\ pstep (TFst _) v =>
        exists w; split; [exact He | eapply ps_fst_pair; eassumption]
    | He : epstep ?x ?w |- exists v, epstep ?x v /\ pstep (TSnd _) v =>
        exists w; split; [exact He | eapply ps_snd_pair; eassumption]
    | He : epstep ?x ?w
        |- exists v, epstep ?x v /\ pstep (TSwitch _ _ _ TEZero) v =>
        exists w; split; [exact He | eapply ps_switch_zero; eassumption]
    end].
  all: try solve [
    match goal with
    | HP : epstep ?P ?Pw, HE : epstep ?E ?Ew
      |- exists v,
        epstep
          (TSigma (TApp ?P TEZero)
            (lift 1 0
              (TEPi ?E
                (TLam (TApp (lift 1 0 ?P) (TESucc (TVar 0))))))) v /\ _ =>
        exists
          (TSigma (TApp Pw TEZero)
            (lift 1 0
              (TEPi Ew
                (TLam (TApp (lift 1 0 Pw) (TESucc (TVar 0)))))));
        split;
        [ eta_congruence
        | eapply ps_epi_cons; eassumption ]
    | HA : epstep ?A ?Aw, HB : epstep ?B ?Bw, HX : epstep ?X ?Xw
      |- exists v,
        epstep (TSigma (TInterp ?A ?X) (lift 1 0 (TInterp ?B ?X))) v /\ _ =>
        exists (TSigma (TInterp Aw Xw) (lift 1 0 (TInterp Bw Xw)));
        split;
        [ eta_congruence
        | eapply ps_interp_prod; eassumption ]
    | HS : epstep ?S ?Sw, HT : epstep ?T ?Tw, HX : epstep ?X ?Xw
      |- exists v,
        epstep
          (TPi ?S
            (TInterp (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X))) v /\ _ =>
        exists
          (TPi Sw
            (TInterp (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)));
        split;
        [ eta_congruence
        | eapply ps_interp_pi; eassumption ]
    | HS : epstep ?S ?Sw, HT : epstep ?T ?Tw, HX : epstep ?X ?Xw
      |- exists v,
        epstep
          (TSigma ?S
            (TInterp (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X))) v /\ _ =>
        exists
          (TSigma Sw
            (TInterp (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)));
        split;
        [ eta_congruence
        | eapply ps_interp_sig; eassumption ]
    | HE : epstep ?E ?Ew, HT : epstep ?T ?Tw, HX : epstep ?X ?Xw
      |- exists v,
        epstep
          (TSigma (TEnumT ?E)
            (TInterp (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X))) v /\ _ =>
        exists
          (TSigma (TEnumT Ew)
            (TInterp (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)));
        split;
        [ eta_congruence
        | eapply ps_interp_choice; eassumption ]
    end].
  all: try solve [
    match goal with
    | HE : epstep ?E ?Ew, HP : epstep ?P ?Pw,
      Hps : epstep ?ps ?psw, Hn : epstep ?n ?nw
      |- exists v,
        epstep
          (TSwitch ?E
            (TLam (TApp (lift 1 0 ?P) (TESucc (TVar 0)))) ?ps ?n) v /\ _ =>
        exists
          (TSwitch Ew
            (TLam (TApp (lift 1 0 Pw) (TESucc (TVar 0)))) psw nw);
        split; [eta_congruence | eapply ps_switch_succ; eassumption]
    | HP : epstep ?P ?Pw, Hj : epstep ?j ?jw, Hx : epstep ?x ?xw
      |- exists v, epstep (TApp ?P (TPair ?j ?x)) v /\ _ =>
        exists (TApp Pw (TPair jw xw));
        split; [eta_congruence | eapply ps_iall_var; eassumption]
    | HA : epstep ?A ?Aw, HB : epstep ?B ?Bw,
      HX : epstep ?X ?Xw, Ha : epstep ?a ?aw,
      Hb : epstep ?b ?bw, HP : epstep ?P ?Pw
      |- exists v,
        epstep
          (TSigma (TIAll ?A ?X ?a ?P) (lift 1 0 (TIAll ?B ?X ?b ?P)))
          v /\ _ =>
        exists
          (TSigma (TIAll Aw Xw aw Pw)
            (lift 1 0 (TIAll Bw Xw bw Pw)));
        split; [eta_congruence | eapply ps_iall_prod; eassumption]
    | HS : epstep ?S ?Sw, HT : epstep ?T ?Tw,
      HX : epstep ?X ?Xw, Hf : epstep ?f ?fw,
      HP : epstep ?P ?Pw
      |- exists v,
        epstep
          (TPi ?S
            (TIAll (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X)
              (TApp (lift 1 0 ?f) (TVar 0)) (lift 1 0 ?P))) v /\ _ =>
        exists
          (TPi Sw
            (TIAll (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)
              (TApp (lift 1 0 fw) (TVar 0)) (lift 1 0 Pw)));
        split; [eta_congruence | eapply ps_iall_pi; eassumption]
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      Hx : epstep ?x ?xw, HP : epstep ?P ?Pw
      |- exists v, epstep (TIAll (TApp ?T ?s) ?X ?x ?P) v /\
          pstep (TIAll (TISig _ _) _ _ _) v =>
        match goal with Hs : epstep s ?sw |- _ =>
          exists (TIAll (TApp Tw sw) Xw xw Pw);
          split; [eta_congruence | eapply ps_iall_sig; eassumption]
        end
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      Hx : epstep ?x ?xw, HP : epstep ?P ?Pw
      |- exists v, epstep (TIAll (TApp ?T ?e) ?X ?x ?P) v /\
          pstep (TIAll (TIChoice _ _) _ _ _) v =>
        match goal with He : epstep e ?ew |- _ =>
          exists (TIAll (TApp Tw ew) Xw xw Pw);
          split; [eta_congruence | eapply ps_iall_choice; eassumption]
        end
    end].
  all: try solve [
    match goal with
    | Hh : epstep ?h ?hw, Hj : epstep ?j ?jw, Hx : epstep ?x ?xw
      |- exists v, epstep (TApp (TApp ?h ?j) ?x) v /\ _ =>
        exists (TApp (TApp hw jw) xw);
        split; [eta_congruence | eapply ps_hyps_var; eassumption]
    | HA : epstep ?A ?Aw, HB : epstep ?B ?Bw,
      HX : epstep ?X ?Xw, HP : epstep ?P ?Pw,
      Hh : epstep ?h ?hw, Ha : epstep ?a ?aw, Hb : epstep ?b ?bw
      |- exists v,
        epstep
          (TPair (THyps ?A ?X ?P ?h ?a) (THyps ?B ?X ?P ?h ?b)) v /\ _ =>
        exists
          (TPair (THyps Aw Xw Pw hw aw) (THyps Bw Xw Pw hw bw));
        split; [eta_congruence | eapply ps_hyps_prod; eassumption]
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      HP : epstep ?P ?Pw, Hh : epstep ?h ?hw, Hf : epstep ?f ?fw
      |- exists v,
        epstep
          (TLam
            (THyps (TApp (lift 1 0 ?T) (TVar 0)) (lift 1 0 ?X)
              (lift 1 0 ?P) (lift 1 0 ?h)
              (TApp (lift 1 0 ?f) (TVar 0)))) v /\ _ =>
        exists
          (TLam
            (THyps (TApp (lift 1 0 Tw) (TVar 0)) (lift 1 0 Xw)
              (lift 1 0 Pw) (lift 1 0 hw)
              (TApp (lift 1 0 fw) (TVar 0))));
        split; [eta_congruence | eapply ps_hyps_pi; eassumption]
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      HP : epstep ?P ?Pw, Hh : epstep ?h ?hw, Hx : epstep ?x ?xw
      |- exists v, epstep (THyps (TApp ?T ?s) ?X ?P ?h ?x) v /\
          pstep (THyps (TISig _ _) _ _ _ _) v =>
        match goal with Hs : epstep s ?sw |- _ =>
          exists (THyps (TApp Tw sw) Xw Pw hw xw);
          split; [eta_congruence | eapply ps_hyps_sig; eassumption]
        end
    | HT : epstep ?T ?Tw, HX : epstep ?X ?Xw,
      HP : epstep ?P ?Pw, Hh : epstep ?h ?hw, Hx : epstep ?x ?xw
      |- exists v, epstep (THyps (TApp ?T ?e) ?X ?P ?h ?x) v /\
          pstep (THyps (TIChoice _ _) _ _ _ _) v =>
        match goal with He : epstep e ?ew |- _ =>
          exists (THyps (TApp Tw ew) Xw Pw hw xw);
          split; [eta_congruence | eapply ps_hyps_choice; eassumption]
        end
    end].
  all: try solve [
    match goal with
    | HR : epstep ?R ?Rw, HP : epstep ?P ?Pw,
      Hs : epstep ?s ?sw, Hi : epstep ?i ?iw, Hxs : epstep ?xs ?xsw
      |- exists v,
        epstep
          (TApp (TApp (TApp ?s ?i) ?xs)
            (THyps (TApp ?R ?i) (TMuI ?R) ?P
              (TLam (TLam
                (TInd (lift 2 0 ?R) (lift 2 0 ?P) (lift 2 0 ?s)
                  (TVar 1) (TVar 0)))) ?xs)) v /\ _ =>
        exists
          (TApp (TApp (TApp sw iw) xsw)
            (THyps (TApp Rw iw) (TMuI Rw) Pw
              (TLam (TLam
                (TInd (lift 2 0 Rw) (lift 2 0 Pw) (lift 2 0 sw)
                  (TVar 1) (TVar 0)))) xsw));
        split; [eta_congruence | eapply ps_ind_red; eassumption]
    end].
  all: try solve [solve_computation_root].
  all: try solve [
    match goal with
    | Hb : epstep ?b ?bw, Ha : epstep ?a ?aw
      |- exists v, epstep (subst ?a 0 ?b) v /\ pstep (TApp (TLam _) _) v =>
        exists (subst aw 0 bw); split;
        [ eapply epstep_subst; eassumption
        | eapply ps_beta; eassumption ]
    end].
  all: try solve [
    match goal with
    | IH : forall z,
        epstep (TApp (lift 1 0 ?f) (TVar 0)) z -> _,
      Hfu : epstep ?f ?fu,
      Hea : rtc epstep ?a ?aw,
      Hca : pstep ?a0 ?aw
      |- exists v, rtc epstep (subst ?a 0 ?b) v /\ pstep (TApp ?fu ?a0) v =>
        assert (Hbody : epstep
          (TApp (lift 1 0 f) (TVar 0))
          (TApp (lift 1 0 fu) (TVar 0))) by eta_congruence;
        destruct (IH _ Hbody) as [q [Hbq Hfq]];
        exists (subst aw 0 q); split;
        [ eapply rtc_epstep_subst; eassumption
        | pose proof (pstep_subst _ _ Hfq a0 aw 0 Hca) as Hsub;
          rewrite subst_eta_app_local in Hsub; exact Hsub ]
    end].
  all: try solve [eapply eta_lambda_critical_rtc; eassumption].
  destruct (epbranches_nth_error_fwd bs bs' k c b H8 e)
    as [c1 [b1 [Hnth [Hc1 Hb1]]]].
  assert (Hc_eq : c1 = c) by (eapply epstep_enum_pos_id; eassumption).
  subst c1.
  assert (Ha_eq : a' = a) by (eapply epstep_enum_pos_id; eassumption).
  subst a'.
  destruct (H0 b1 Hb1) as [q [Hbq Hbcore]].
  exists (subst w 0 q). split.
  - eapply rtc_epstep_subst; eassumption.
  - eapply ps_case_red with (k := k) (c := c) (b := b1) (n := n).
    + exact Hnth.
    + exact e0.
    + exact e1.
    + intros j cj' bj' Hj Hnth'.
      destruct (epbranches_nth_error_rev bs bs' j cj' bj' H8 Hnth')
        as [cj [bj [Horig [Hcj Hbj]]]].
      destruct (e2 j cj bj Hj Horig) as [nj [Hpos Hneq]].
      assert (Hcj_eq : cj' = cj) by
        (eapply epstep_enum_pos_id; eassumption).
      subst cj'. exists nj. split; assumption.
    + exact Hcore.
    + exact Hbcore.
Qed.

Corollary pstep_epstep_commute : forall s t u,
    pstep s t -> epstep s u ->
    exists v, rtc epstep t v /\ pstep u v.
Proof.
  intros s t u Hp He.
  exact (proj1 pstep_epstep_commute_mut s t Hp u He).
Qed.

Corollary pbranches_epbranches_commute : forall ss ts us,
    pbranches ss ts -> epbranches ss us ->
    exists vs, rtc epbranches ts vs /\ pbranches us vs.
Proof.
  intros ss ts us Hp He.
  exact (proj2 pstep_epstep_commute_mut ss ts Hp us He).
Qed.

End _tmp_commute.

(* Checked conversion metatheory: _work_mixed_closure *)
Module _work_mixed_closure.
Import _tmp_epstep _tmp_epstep_diamond _tmp_commute.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

(* Push one parallel core step across an arbitrary parallel eta path. *)
Lemma pstep_epsteps_commute : forall x y,
    pstep x y -> forall z, rtc epstep x z ->
    exists w, rtc epstep y w /\ rtc pstep z w.
Proof.
  intros x y Hxy z Hxz. revert y Hxy.
  induction Hxz as [x | x z1 z Hxz1 Hrest IH]; intros y Hxy.
  - exists y. split; [apply rtc_refl | apply rtc_one; exact Hxy].
  - destruct (pstep_epstep_commute _ _ _ Hxy Hxz1)
      as [q [Hyq Hz1q]].
    destruct (IH q Hz1q) as [w [Hqw Hzw]].
    exists w. split.
    + eapply rtc_trans; eassumption.
    + exact Hzw.
Qed.

(* Push an arbitrary core path across an arbitrary eta path. *)
Lemma psteps_epsteps_commute : forall x y,
    rtc pstep x y -> forall z, rtc epstep x z ->
    exists w, rtc epstep y w /\ rtc pstep z w.
Proof.
  intros x y Hxy z Hxz. revert z Hxz.
  induction Hxy as [x | x y1 y Hxy1 Hrest IH]; intros z Hxz.
  - exists z. split; [exact Hxz | apply rtc_refl].
  - destruct (pstep_epsteps_commute _ _ Hxy1 _ Hxz)
      as [q [Hy1q Hzq]].
    destruct (IH q Hy1q) as [w [Hyw Hqw]].
    exists w. split.
    + exact Hyw.
    + eapply rtc_trans; eassumption.
Qed.

(* One phase is an arbitrary block of either kind.  Treating whole blocks
   as single phases turns Hindley--Rosen commutation into an ordinary
   diamond argument. *)
Inductive cstep : term -> term -> Prop :=
| cs_core : forall t u, rtc pstep t u -> cstep t u
| cs_eta : forall t u, rtc epstep t u -> cstep t u.

Lemma cstep_refl : forall t, cstep t t.
Proof. intros t. apply cs_core, rtc_refl. Qed.

Lemma cstep_diamond : diamond cstep.
Proof.
  unfold diamond. intros x y z Hxy Hxz.
  destruct Hxy as [x y Hxy | x y Hxy];
    destruct Hxz as [x z Hxz | x z Hxz].
  - destruct (pstep_confluent x y z Hxy Hxz) as [w [Hyw Hzw]].
    exists w. split; apply cs_core; assumption.
  - destruct (psteps_epsteps_commute _ _ Hxy _ Hxz)
      as [w [Hyw Hzw]].
    exists w. split; [apply cs_eta | apply cs_core]; assumption.
  - destruct (psteps_epsteps_commute _ _ Hxz _ Hxy)
      as [w [Hzw Hyw]].
    exists w. split; [apply cs_core | apply cs_eta]; assumption.
  - pose proof (diamond_rtc_confluent _ epstep epstep_diamond) as Heta.
    destruct (Heta x y z Hxy Hxz) as [w [Hyw Hzw]].
    exists w. split; apply cs_eta; assumption.
Qed.

Lemma cstep_confluent : confluent cstep.
Proof. apply diamond_rtc_confluent, cstep_diamond. Qed.

Lemma pstep_cstep : forall t u, pstep t u -> cstep t u.
Proof. intros t u H. apply cs_core, rtc_one, H. Qed.

Lemma epstep_cstep : forall t u, epstep t u -> cstep t u.
Proof. intros t u H. apply cs_eta, rtc_one, H. Qed.


End _work_mixed_closure.

(* Checked conversion metatheory: _luna_fstep_split *)
Module _luna_fstep_split.
Import _tmp_epstep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma epbranches_replace_label_luna : forall bs1 c c' b bs2,
    epstep c c' ->
    epbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c',b) :: bs2).
Proof.
  induction bs1 as [|[d e] bs1 IH]; intros c c' b bs2 Hcc'; cbn.
  - constructor; [exact Hcc' | apply epstep_refl | apply epbranches_refl].
  - constructor;
      [apply epstep_refl | apply epstep_refl | apply IH; exact Hcc'].
Qed.

Lemma pbranches_replace_body_luna : forall bs1 c b b' bs2,
    pstep b b' ->
    pbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c,b') :: bs2).
Proof.
  induction bs1 as [|[d e] bs1 IH]; intros c b b' bs2 Hbb'; cbn.
  - constructor; [apply pstep_refl | exact Hbb' | apply pbranches_refl].
  - constructor;
      [apply pstep_refl | apply pstep_refl | apply IH; exact Hbb'].
Qed.

Lemma epbranches_replace_body_luna : forall bs1 c b b' bs2,
    epstep b b' ->
    epbranches (bs1 ++ (c,b) :: bs2) (bs1 ++ (c,b') :: bs2).
Proof.
  induction bs1 as [|[d e] bs1 IH]; intros c b b' bs2 Hbb'; cbn.
  - constructor; [apply epstep_refl | exact Hbb' | apply epbranches_refl].
  - constructor;
      [apply epstep_refl | apply epstep_refl | apply IH; exact Hbb'].
Qed.

Lemma fstep_pstep_or_epstep : forall t u,
    fstep t u -> pstep t u \/ epstep t u.
Proof.
  intros t u H.
  induction H;
    try solve [left; apply step_pstep; exact H];
    try solve [right; apply eps_eta; apply epstep_refl];
    try solve [
      match goal with
      | Hih : pstep _ _ \/ epstep _ _ |- _ => destruct Hih as [Hp|He]
      end;
      [ left; econstructor; eauto using pstep_refl, pbranches_refl
      | right; econstructor; eauto using epstep_refl, epbranches_refl ]
    ];
    try solve [
      match goal with
      | Hih : pstep _ _ \/ epstep _ _ |- _ => destruct Hih as [Hp|He]
      end;
      [ left; eapply ps_case; eauto using pstep_refl, pbranches_refl;
        apply pbranches_replace_label; exact Hp
      | right; eapply eps_case; eauto using epstep_refl, epbranches_refl;
        apply epbranches_replace_label_luna; exact He ]
    ];
    try solve [
      match goal with
      | Hih : pstep _ _ \/ epstep _ _ |- _ => destruct Hih as [Hp|He]
      end;
      [ left; eapply ps_case; eauto using pstep_refl, pbranches_refl;
        apply pbranches_replace_body_luna; exact Hp
      | right; eapply eps_case; eauto using epstep_refl, epbranches_refl;
        apply epbranches_replace_body_luna; exact He ]
    ].
Qed.

End _luna_fstep_split.

(* Checked conversion metatheory: _work_cjoin *)
Module _work_cjoin.
Import _tmp_epstep _work_mixed_closure _luna_fstep_split.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Definition cjoin (t u : term) : Prop :=
  exists w, rtc cstep t w /\ rtc cstep u w.

Lemma cjoin_refl : forall t, cjoin t t.
Proof. intros t. exists t. split; apply rtc_refl. Qed.

Lemma cjoin_sym : forall t u, cjoin t u -> cjoin u t.
Proof. intros t u [w [Htw Huw]]. exists w. auto. Qed.

Lemma cjoin_trans : forall t u v,
    cjoin t u -> cjoin u v -> cjoin t v.
Proof.
  intros t u v [q [Htq Huq]] [r [Hur Hvr]].
  destruct (cstep_confluent u q r Huq Hur) as [w [Hqw Hrw]].
  exists w. split; eapply rtc_trans; eassumption.
Qed.

Lemma cjoin_reduce_left : forall t u t',
    cjoin t u -> rtc cstep t t' -> cjoin t' u.
Proof.
  intros t u t' [q [Htq Huq]] Htt'.
  destruct (cstep_confluent t q t' Htq Htt') as [w [Hqw Ht'w]].
  exists w. split; [exact Ht'w |].
  eapply rtc_trans; eassumption.
Qed.

Lemma cjoin_reduce_right : forall t u u',
    cjoin t u -> rtc cstep u u' -> cjoin t u'.
Proof.
  intros t u u' Hjoin Huu'. apply cjoin_sym.
  eapply cjoin_reduce_left; [apply cjoin_sym; exact Hjoin | exact Huu'].
Qed.

Lemma fstep_cstep : forall t u, fstep t u -> cstep t u.
Proof.
  intros t u H.
  destruct (fstep_pstep_or_epstep _ _ H) as [Hp | He].
  - apply pstep_cstep, Hp.
  - apply epstep_cstep, He.
Qed.

Lemma fconv_cjoin : forall t u, fconv t u -> cjoin t u.
Proof.
  intros t u H. induction H.
  - exists u. split; [apply rtc_one, fstep_cstep, H | apply rtc_refl].
  - apply cjoin_refl.
  - apply cjoin_sym, IHfconv.
  - eapply cjoin_trans; eassumption.
Qed.

Lemma conv_phi_cjoin : forall t u, conv t u ->
    cjoin (phi_erase t) (phi_erase u).
Proof.
  intros t u H. apply fconv_cjoin, phi_erase_conv, H.
Qed.


End _work_cjoin.

(* Checked conversion metatheory: _luna_parallel_hshape *)
Module _luna_parallel_hshape.
Import _tmp_epstep.
From Stdlib Require Import List.
Import ListNotations TypeRulesCore.

Lemma pstep_hshape_luna : forall t u h,
    pstep t u -> hshape t h -> hshape u h.
Proof.
  intros t u h Hp Hshape.
  inversion Hp; subst; inversion Hshape; subst; eauto using hshape;
    repeat match goal with
    | H : pstep (TMuI _) _ |- _ => inversion H; subst; clear H
    | H : pstep (TMuS _) _ |- _ => inversion H; subst; clear H
    end;
    constructor.
Qed.

Lemma epstep_hshape_luna : forall t u h,
    epstep t u -> hshape t h -> hshape u h.
Proof.
  intros t u h He Hshape.
  inversion He; subst; inversion Hshape; subst; eauto using hshape;
    repeat match goal with
    | H : epstep (TMuI _) _ |- _ => inversion H; subst; clear H
    | H : epstep (TMuS _) _ |- _ => inversion H; subst; clear H
    end;
    constructor.
Qed.


End _luna_parallel_hshape.

(* Checked conversion metatheory: _tmp_epbranches_nth *)
Module _tmp_epbranches_nth.
Import _tmp_epstep.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma epbranches_nth_error : forall bs bs' k c b,
  epbranches bs bs' -> nth_error bs k = Some (c,b) ->
  exists c' b', nth_error bs' k = Some (c',b') /\ epstep c c' /\ epstep b b'.
Proof.
  intros bs bs' k c b Hbranches.
  revert k c b.
  induction Hbranches as [| x x' y y' bs bs' Hc Hb Htail IH].
  - intros k c b Hnth. destruct k; cbn in Hnth; discriminate.
  - intros k c0 b0 Hnth.
    destruct k as [|k].
    + cbn in Hnth. inversion Hnth; subst c0 b0.
      exists x', y'. repeat split; assumption.
    + cbn in Hnth.
      destruct (IH k c0 b0 Hnth) as [c0' [b0' [Hnth' [Hc0 Hb0]]]].
      exists c0', b0'. repeat split; assumption.
Qed.

End _tmp_epbranches_nth.

(* Checked conversion metatheory: _luna_rtc_epbranches_nth *)
Module _luna_rtc_epbranches_nth.
Import _tmp_epstep _tmp_epbranches_nth _work_epstep_rtc.
From Stdlib Require Import List.
Import ListNotations TypeRulesCore.

(* A branch tag can move along epstep (the eta constructor is an
   explicit counterexample to tag preservation), so the sound closure
   statement keeps the endpoint tag and records its epstep path. *)
Lemma rtc_epbranches_nth_error_fwd_luna :
    forall bs bs' k c b,
      rtc epbranches bs bs' ->
      nth_error bs k = Some (c,b) ->
      exists c' b',
        nth_error bs' k = Some (c',b') /\
        rtc epstep c c' /\ rtc epstep b b'.
Proof.
  intros bs bs' k c b Hrtc.
  revert k c b.
  induction Hrtc as [bs | bs bs1 bs' Hhead Htail IH].
  - intros k c b Hnth.
    exists c, b. repeat split; [exact Hnth | apply rtc_refl | apply rtc_refl].
  - intros k c b Hnth.
    (* First transport the selected entry through the one-step branch
       relation, then apply the induction hypothesis to the tail. *)
    destruct (epbranches_nth_error bs bs1 k c b Hhead Hnth)
      as [c1 [b1 [Hidx1 [Hc1 Hb1]]]].
    destruct (IH k c1 b1 Hidx1)
      as [c' [b' [Hidx [Hc' Hb']]]].
    eexists c', b'. repeat split; [exact Hidx | |].
    + eapply rtc_trans; [exact (rtc_step Hc1 rtc_refl) | exact Hc'].
    + eapply rtc_trans; [exact (rtc_step Hb1 rtc_refl) | exact Hb'].
Qed.

(* The exact same-tag corollary is valid once the tag is known to be an
   enum position.  This is the form used by case-selection arguments. *)
Lemma epstep_enum_pos_id_luna : forall c c' n,
    epstep c c' -> enum_pos c n -> c' = c.
Proof.
  intros c c' n Hstep Hpos. revert c' Hstep.
  induction Hpos as [|c n Hpos IH]; intros c' Hstep.
  - inversion Hstep; reflexivity.
  - inversion Hstep; subst; f_equal; eauto.
Qed.

Lemma rtc_epstep_enum_pos_id_luna : forall c c' n,
    rtc epstep c c' -> enum_pos c n -> c' = c.
Proof.
  intros c c' n Hrtc Hpos. revert n Hpos.
  induction Hrtc as [c | c d c' Hstep Htail IH].
  - intros n Hpos; reflexivity.
  - intros n Hpos.
    pose proof (epstep_enum_pos_id_luna c d n Hstep Hpos) as Hcd.
    subst d. exact (IH n Hpos).
Qed.

Lemma rtc_epbranches_nth_error_fwd_tag_luna :
    forall bs bs' k c b n,
      rtc epbranches bs bs' ->
      nth_error bs k = Some (c,b) ->
      enum_pos c n ->
      exists b',
        nth_error bs' k = Some (c,b') /\ rtc epstep b b'.
Proof.
  intros bs bs' k c b n Hrtc Hnth Hpos.
  destruct (rtc_epbranches_nth_error_fwd_luna bs bs' k c b Hrtc Hnth)
    as [c' [b' [Hidx [Hc Hb]]]].
  pose proof (rtc_epstep_enum_pos_id_luna c c' n Hc Hpos) as Heq.
  subst c'. eexists; split; [exact Hidx | exact Hb].
Qed.

End _luna_rtc_epbranches_nth.

(* Checked conversion metatheory: _work_cstep_invariants *)
Module _work_cstep_invariants.
Import _tmp_epstep _work_mixed_closure _work_cjoin _luna_parallel_hshape _luna_rtc_epbranches_nth.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma rtc_pstep_hshape : forall t u,
    rtc pstep t u -> forall h, hshape t h -> hshape u h.
Proof.
  intros t u H. induction H; intros h Hshape.
  - exact Hshape.
  - apply IHrtc. eapply pstep_hshape_luna; eassumption.
Qed.

Lemma rtc_epstep_hshape : forall t u,
    rtc epstep t u -> forall h, hshape t h -> hshape u h.
Proof.
  intros t u H. induction H; intros h Hshape.
  - exact Hshape.
  - apply IHrtc. eapply epstep_hshape_luna; eassumption.
Qed.

Lemma cstep_hshape : forall t u,
    cstep t u -> forall h, hshape t h -> hshape u h.
Proof.
  intros t u H h Hshape. destruct H.
  - eapply rtc_pstep_hshape; eassumption.
  - eapply rtc_epstep_hshape; eassumption.
Qed.

Lemma rtc_cstep_hshape : forall t u,
    rtc cstep t u -> forall h, hshape t h -> hshape u h.
Proof.
  intros t u H. induction H; intros h Hshape.
  - exact Hshape.
  - apply IHrtc. eapply cstep_hshape; eassumption.
Qed.

Lemma pstep_enumt_inv_local : forall E u, pstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ pstep E E'.
Proof. intros E u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_enumt_inv : forall E u, rtc pstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ rtc pstep E E'.
Proof.
  intros E u H. remember (TEnumT E) as t eqn:Ht. revert E Ht.
  induction H; intros E HE; subst.
  - exists E. split; [reflexivity | apply rtc_refl].
  - destruct (pstep_enumt_inv_local E y H) as [E1 [-> HE1]].
    destruct (IHrtc E1 eq_refl) as [E2 [-> HE2]].
    exists E2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Lemma epstep_enumt_inv_local : forall E u, epstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ epstep E E'.
Proof. intros E u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_enumt_inv : forall E u, rtc epstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ rtc epstep E E'.
Proof.
  intros E u H. remember (TEnumT E) as t eqn:Ht. revert E Ht.
  induction H; intros E HE; subst.
  - exists E. split; [reflexivity | apply rtc_refl].
  - destruct (epstep_enumt_inv_local E y H) as [E1 [-> HE1]].
    destruct (IHrtc E1 eq_refl) as [E2 [-> HE2]].
    exists E2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Lemma cstep_enumt_inv : forall E u, cstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ cstep E E'.
Proof.
  intros E u H. inversion H; subst.
  - destruct (rtc_pstep_enumt_inv _ _ H0) as [E' [-> HE']].
    exists E'. split; [reflexivity | apply cs_core, HE'].
  - destruct (rtc_epstep_enumt_inv _ _ H0) as [E' [-> HE']].
    exists E'. split; [reflexivity | apply cs_eta, HE'].
Qed.

Lemma rtc_cstep_enumt_inv : forall E u, rtc cstep (TEnumT E) u ->
    exists E', u = TEnumT E' /\ rtc cstep E E'.
Proof.
  intros E u H. remember (TEnumT E) as t eqn:Ht. revert E Ht.
  induction H; intros E HE; subst.
  - exists E. split; [reflexivity | apply rtc_refl].
  - destruct (cstep_enumt_inv E y H) as [E1 [-> HE1]].
    destruct (IHrtc E1 eq_refl) as [E2 [-> HE2]].
    exists E2. split; [reflexivity | eapply rtc_step; eassumption].
Qed.

Lemma pstep_pi_inv_local : forall A B u, pstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_pi_inv : forall A B u, rtc pstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TPi A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_pi_inv_local A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_pi_inv_local : forall A B u, epstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_pi_inv : forall A B u, rtc epstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TPi A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_pi_inv_local A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_pi_inv : forall A B u, cstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_pi_inv _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_pi_inv _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_pi_inv : forall A B u, rtc cstep (TPi A B) u ->
    exists A' B', u = TPi A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TPi A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_pi_inv A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_pi_inv : forall A1 B1 A2 B2,
    cjoin (TPi A1 B1) (TPi A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_pi_inv _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_pi_inv _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.

Lemma rtc_pstep_sort_id : forall k u,
    rtc pstep (TSort k) u -> u = TSort k.
Proof.
  intros k u H. remember (TSort k) as t eqn:Ht.
  induction H; subst; [reflexivity |].
  inversion H; subst. apply IHrtc. reflexivity.
Qed.

Lemma rtc_epstep_sort_id : forall k u,
    rtc epstep (TSort k) u -> u = TSort k.
Proof.
  intros k u H. remember (TSort k) as t eqn:Ht.
  induction H; subst; [reflexivity |].
  inversion H; subst. apply IHrtc. reflexivity.
Qed.

Lemma cstep_sort_id : forall k u, cstep (TSort k) u -> u = TSort k.
Proof.
  intros k u H. inversion H; subst.
  - eapply rtc_pstep_sort_id, H0.
  - eapply rtc_epstep_sort_id, H0.
Qed.

Lemma rtc_cstep_sort_id : forall k u,
    rtc cstep (TSort k) u -> u = TSort k.
Proof.
  intros k u H. remember (TSort k) as t eqn:Ht.
  induction H.
  - now inversion Ht.
  - subst x.
    assert (Hy : y = TSort k) by (eapply cstep_sort_id; eassumption).
    subst y. apply IHrtc. reflexivity.
Qed.

Lemma rtc_pstep_enum_pos_id : forall c d n,
    rtc pstep c d -> enum_pos c n -> d = c.
Proof.
  intros c d n H. revert n.
  induction H; intros n Hpos; [reflexivity |].
  assert (Hyx : y = x) by (eapply pstep_enum_pos_id; eassumption).
  subst y. rewrite (IHrtc n Hpos). reflexivity.
Qed.

Lemma cstep_enum_pos_id : forall c d n,
    cstep c d -> enum_pos c n -> d = c.
Proof.
  intros c d n H Hpos. destruct H.
  - eapply rtc_pstep_enum_pos_id; eassumption.
  - eapply rtc_epstep_enum_pos_id_luna; eassumption.
Qed.

Lemma rtc_cstep_enum_pos_id : forall c d n,
    rtc cstep c d -> enum_pos c n -> d = c.
Proof.
  intros c d n H. revert n.
  induction H; intros n Hpos; [reflexivity |].
  assert (Hyx : y = x) by (eapply cstep_enum_pos_id; eassumption).
  subst y. rewrite (IHrtc n Hpos). reflexivity.
Qed.

End _work_cstep_invariants.

(* Checked conversion metatheory: _luna_phi_erase_shapes *)
Module _luna_phi_erase_shapes.

From Stdlib Require Import List.
Import ListNotations TypeRulesCore.

Lemma phi_erase_hshape_luna : forall t h,
    hshape t h -> hshape (phi_erase t) h.
Proof.
  intros t h Hshape. induction Hshape; cbn [phi_erase]; constructor.
Qed.

Lemma phi_erase_eval_luna : forall t u,
    eval t u -> eval (phi_erase t) (phi_erase u).
Proof.
  intros t u Heval. induction Heval.
  - apply ev_refl.
  - eapply ev_step.
    + apply phi_erase_step. exact H.
    + exact IHHeval.
Qed.


End _luna_phi_erase_shapes.

(* Checked conversion metatheory: _work_conv_whd_pos *)
Module _work_conv_whd_pos.
Import _work_mixed_closure _work_cjoin _work_cstep_invariants _luna_phi_erase_shapes.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRulesCore.

Lemma phi_erase_eval_csteps : forall t u, eval t u ->
    rtc cstep (phi_erase t) (phi_erase u).
Proof.
  intros t u H.
  apply rtc_one, cs_core, eval_psteps, phi_erase_eval_luna, H.
Qed.

Theorem conv_whd_proved : forall t u h1 h2,
    conv t u -> whd t h1 -> whd u h2 -> h1 = h2.
Proof.
  intros t u h1 h2 Hconv [t' [Ht Htshape]] [u' [Hu Hushape]].
  pose proof (conv_phi_cjoin _ _ Hconv) as Hjoin.
  pose proof (phi_erase_eval_csteps _ _ Ht) as Htred.
  pose proof (phi_erase_eval_csteps _ _ Hu) as Hured.
  assert (Hjoin' : cjoin (phi_erase t') (phi_erase u')).
  { eapply cjoin_reduce_right.
    - eapply cjoin_reduce_left; eassumption.
    - exact Hured. }
  destruct Hjoin' as [w [Htw Huw]].
  eapply hshape_tag_unique with (T := w).
  - eapply rtc_cstep_hshape; [exact Htw |].
    apply phi_erase_hshape_luna, Htshape.
  - eapply rtc_cstep_hshape; [exact Huw |].
    apply phi_erase_hshape_luna, Hushape.
Qed.

Theorem conv_pos_proved : forall c d n m,
    conv c d -> enum_pos c n -> enum_pos d m -> n = m.
Proof.
  intros c d n m Hconv Hc Hd.
  destruct (conv_phi_cjoin _ _ Hconv) as [w [Hcw Hdw]].
  pose proof (phi_erase_enum_pos _ _ Hc) as Hec.
  pose proof (phi_erase_enum_pos _ _ Hd) as Hed.
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hcw Hec) as Ewc.
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hdw Hed) as Ewd.
  assert (Ecd : phi_erase c = phi_erase d) by congruence.
  eapply enum_pos_functional.
  - exact Hec.
  - rewrite Ecd. exact Hed.
Qed.

End _work_conv_whd_pos.

Import _work_conv_whd_pos _work_cstep_invariants _work_cjoin.

(* ------------------------------------------------------------------ *)
(*  Conversion facts                                                     *)
(* ------------------------------------------------------------------ *)

(* Conversion preserves classified weak-head shapes. *)
Theorem conv_whd : forall t u h1 h2,
    conv t u -> whd t h1 -> whd u h2 -> h1 = h2.
Proof. exact conv_whd_proved. Qed.

(* The progress proof needs only this stable-head contradiction. *)
Lemma conv_enumt_cons_nil_absurd : forall tg E,
    conv (TEnumT (TConsE tg E)) (TEnumT TNilE) -> False.
Proof.
  intros tg E Hc.
  destruct (conv_phi_cjoin _ _ Hc) as [w [HL HR]].
  destruct (rtc_cstep_enumt_inv _ _ HL) as [L [EL HL']].
  destruct (rtc_cstep_enumt_inv _ _ HR) as [R [ER HR']].
  rewrite EL in ER. inversion ER; subst R.
  pose proof (rtc_cstep_hshape _ _ HL' HConsE (hs_conse _ _)) as HC.
  pose proof (rtc_cstep_hshape _ _ HR' HNilE hs_nile) as HN.
  pose proof (hshape_tag_unique _ _ _ HC HN). discriminate.
Qed.

(* conversion-related canonical positions are the same position *)
Theorem conv_pos : forall c d n m,
    conv c d -> enum_pos c n -> enum_pos d m -> n = m.
Proof. exact conv_pos_proved. Qed.

(* A membership walk and a coverage walk can expose different reducts of
   the same list.  Parallel confluence aligns those reducts componentwise. *)
Lemma spine_mem_covers_join : forall a L1,
    spine_mem a L1 -> forall Psi L2,
    covers Psi L2 -> pjoin L1 L2 ->
    exists d, In d Psi /\ conv a d.
Proof.
  intros a L1 Hmem.
  induction Hmem as
      [Phi A c Phi' Heval Hac
      |Phi A c Phi' Heval Htail IH];
    intros Psi L2 Hcov Hjoin;
    pose proof (pjoin_eval_left _ _ _ Hjoin Heval) as Hleft;
    inversion Hcov; subst.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth)
      as [_ [Hlabels _]].
    apply Exists_exists in H0.
    destruct H0 as [d [Hdin Hcd]].
    exists d. split; [exact Hdin |].
    eapply cv_trans; [exact Hac |].
    eapply cv_trans; [apply pjoin_conv; exact Hlabels | exact Hcd].
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth)
      as [_ [_ Htails]].
    eapply IH; eassumption.
Qed.

Lemma spine_covered : forall L a Psi,
    spine_mem a L -> covers Psi L -> exists d, In d Psi /\ conv a d.
Proof.
  intros L a Psi Hmem Hcov.
  eapply spine_mem_covers_join; eauto using pjoin_refl.
Qed.

(* The application classification uses only erased sort observations.
   It does not require Pi injectivity or reflection through phi_erase. *)
Module MuApplicationSort.
Import TypeRulesCore ListNotations _tmp_epstep _tmp_epstep_subst
  _work_mixed_closure _work_cjoin _work_cstep_invariants
  _work_conv_whd_pos _luna_phi_erase_shapes.

Definition erased_sort (T : term) : Prop :=
  exists j, cjoin (phi_erase T) (TSort j).

Lemma erased_sort_sub : forall G T U, sub G T U ->
    erased_sort T -> erased_sort U.
Proof.
  intros G T U Hsub. induction Hsub; intros [n Hn].
  - (* conversion *)
    exists n. eapply cjoin_trans.
    + apply cjoin_sym. apply conv_phi_cjoin. exact H.
    + exact Hn.
  - (* transitivity *)
    eapply IHHsub2. eapply IHHsub1. exists n. exact Hn.
  - (* sort *)
    exists k. apply cjoin_refl.
  - (* Pi subtyping cannot reach a sort *)
    exfalso.
    destruct Hn as [w [Htw Hws]].
    assert (HP : hshape w HPi).
    { eapply rtc_cstep_hshape; [exact Htw |].
      apply phi_erase_hshape_luna. constructor. }
    assert (HS : hshape w HSort).
    { eapply rtc_cstep_hshape; [exact Hws |]. constructor. }
    pose proof (hshape_tag_unique w _ _ HP HS) as K. discriminate K.
  - (* forgetting μˢ to Carrier *)
    exfalso.
    destruct Hn as [w [Htw Hws]].
    assert (HP : hshape w HMuSApp).
    { eapply rtc_cstep_hshape; [exact Htw |].
      apply phi_erase_hshape_luna. constructor. }
    assert (HS : hshape w HSort).
    { eapply rtc_cstep_hshape; [exact Hws |]. constructor. }
    pose proof (hshape_tag_unique w _ _ HP HS) as K. discriminate K.
  - (* signature subtyping *)
    exfalso.
    destruct Hn as [w [Htw Hws]].
    assert (HP : hshape w HMuSApp).
    { eapply rtc_cstep_hshape; [exact Htw |].
      apply phi_erase_hshape_luna. constructor. }
    assert (HS : hshape w HSort).
    { eapply rtc_cstep_hshape; [exact Hws |]. constructor. }
    pose proof (hshape_tag_unique w _ _ HP HS) as K. discriminate K.
Qed.

Lemma erased_sort_whd : forall T U h,
    erased_sort T -> conv T U -> whd U h -> h = HSort.
Proof.
  intros T U h [j Htj] Hconv [U' [HU HUshape]].
  pose proof (conv_phi_cjoin _ _ Hconv) as Htu.
  pose proof (phi_erase_eval_csteps _ _ HU) as Hured.
  destruct (cjoin_reduce_right _ _ _ Htu Hured) as [w [Htw Huw]].
  (* The left endpoint also joins the erased source to the sort. *)
  destruct (cjoin_reduce_left _ _ _ Htj Htw) as [z [Hz1 Hz2]].
  pose proof (rtc_cstep_sort_id j z Hz2) as ->.
  assert (HS : hshape (TSort j) HSort) by constructor.
  assert (HUh : hshape (TSort j) h).
  { eapply rtc_cstep_hshape; [eapply rtc_trans; [exact Huw | exact Hz1] |].
    apply phi_erase_hshape_luna, HUshape. }
  pose proof (hshape_tag_unique (TSort j) _ _ HS HUh) as K.
  destruct h; simpl in K; try discriminate; reflexivity.
Qed.




Lemma rtc_epstep_subst_luna : forall t t' a k,
    rtc epstep t t' ->
    rtc epstep (subst a k t) (subst a k t').
Proof.
  intros t t' a k Ht. induction Ht as [x | x y z Hxy Hyz IH].
  - apply rtc_refl.
  - eapply rtc_step.
    + eapply epstep_subst; [exact Hxy | apply epstep_refl].
    + exact IH.
Qed.

Lemma rtc_pstep_subst_luna : forall t t' a k,
    rtc pstep t t' ->
    rtc pstep (subst a k t) (subst a k t').
Proof.
  intros t t' a k Ht. induction Ht as [x | x y z Hxy Hyz IH].
  - apply rtc_refl.
  - eapply rtc_step; [eapply pstep_subst; [exact Hxy | apply pstep_refl] | exact IH].
Qed.

Lemma rtc_cstep_subst_luna : forall t t' a k,
    rtc cstep t t' ->
    rtc cstep (subst a k t) (subst a k t').
Proof.
  intros t t' a k Ht. induction Ht as [x | x y z Hxy Hyz IH].
  - apply rtc_refl.
  - eapply rtc_step.
    + destruct Hxy as [Hp | He].
      * apply cs_core. eapply rtc_pstep_subst_luna; exact r.
      * apply cs_eta. eapply rtc_epstep_subst_luna; exact r.
    + exact IH.
Qed.

Lemma erased_sort_cjoin_subst_luna : forall B a j,
    cjoin (phi_erase B) (TSort j) ->
    cjoin (phi_erase (subst a 0 B)) (TSort j).
Proof.
  intros B a j [w [HB Hw]].
  pose proof (rtc_cstep_sort_id j w Hw) as ->.
  rewrite phi_erase_subst.
  assert (Hs : rtc cstep
      (subst (phi_erase a) 0 (phi_erase B))
      (subst (phi_erase a) 0 (TSort j))).
  { eapply rtc_cstep_subst_luna; exact HB. }
  cbn [subst] in Hs.
  exists (TSort j). split; [exact Hs | apply rtc_refl].
Qed.





Lemma luna_check_mui_synth : forall G t T,
    check G t T ->
    forall R, t = TMuI R ->
    exists IT, synth G (TMuI R) (TPi IT (TSort 0)) /\
               (conv (TPi IT (TSort 0)) T \/
                sub G (TPi IT (TSort 0)) T).
Proof.
  intros G t T Hck. induction Hck; intros Rq Ht; subst; try discriminate.
  - inversion H; subst. eexists. split; [eassumption | left; eassumption].
  - destruct (IHHck Rq eq_refl) as [IT [Hsyn Hrel]].
    exists IT. split; [exact Hsyn |].
    destruct Hrel as [Hrel | Hrel].
    + right. eapply su_trans; [apply su_conv; exact Hrel | eassumption].
    + right. eapply su_trans; eassumption.
  - destruct (IHHck Rq eq_refl) as [IT [Hsyn Hrel]].
    exists IT. split; [exact Hsyn | right].
    destruct Hrel as [Hrel | Hrel].
    + eapply su_trans; [apply su_conv; exact Hrel | apply su_conv, cv_sym; exact H].
    + eapply su_trans; [exact Hrel | apply su_conv, cv_sym; exact H].
Qed.

Lemma luna_check_mus_synth : forall G t T,
    check G t T ->
    forall Sf, t = TMuS Sf ->
    exists IT, synth G (TMuS Sf) (TPi IT (TSort 0)) /\
               (conv (TPi IT (TSort 0)) T \/
                sub G (TPi IT (TSort 0)) T).
Proof.
  intros G t T Hck. induction Hck; intros Sfq Ht; subst; try discriminate.
  - inversion H; subst. eexists. split; [eassumption | left; eassumption].
  - destruct (IHHck Sfq eq_refl) as [IT [Hsyn Hrel]].
    exists IT. split; [exact Hsyn |].
    destruct Hrel as [Hrel | Hrel].
    + right. eapply su_trans; [apply su_conv; exact Hrel | eassumption].
    + right. eapply su_trans; eassumption.
  - destruct (IHHck Sfq eq_refl) as [IT [Hsyn Hrel]].
    exists IT. split; [exact Hsyn | right].
    destruct Hrel as [Hrel | Hrel].
    + eapply su_trans; [apply su_conv; exact Hrel | apply su_conv, cv_sym; exact H].
    + eapply su_trans; [exact Hrel | apply su_conv, cv_sym; exact H].
Qed.

Lemma mu_former_checked_erased_pi_origin_luna : forall G f A B,
    (exists R, f = TMuI R) \/ (exists Sf, f = TMuS Sf) ->
    check G f (TPi A B) ->
    exists IT, sub G (TPi IT (TSort 0)) (TPi A B).
Proof.
  intros G f A B [ [R ->] | [Sf ->] ] Hf.
  - destruct (luna_check_mui_synth G (TMuI R) (TPi A B) Hf R eq_refl)
      as [IT [Hsyn [Hconv | Hsub]]].
    + exists IT. apply su_conv. exact Hconv.
    + exists IT. exact Hsub.
  - destruct (luna_check_mus_synth G (TMuS Sf) (TPi A B) Hf Sf eq_refl)
      as [IT [Hsyn [Hconv | Hsub]]].
    + exists IT. apply su_conv. exact Hconv.
    + exists IT. exact Hsub.
Qed.



Lemma cjoin_hshape_tags_parent : forall t u h k,
  cjoin t u -> hshape t h -> hshape u k -> h = k.
Proof.
  intros t u h k [w [Ht Hu]] HH HK.
  eapply hshape_tag_unique with (T:=w).
  - eapply rtc_cstep_hshape; [exact Ht | exact HH].
  - eapply rtc_cstep_hshape; [exact Hu | exact HK].
Qed.

Definition erased_pi_sort (T : term) : Prop :=
  forall A B, cjoin (phi_erase T) (TPi A B) ->
    exists j, cjoin B (TSort j).

Lemma erased_pi_sort_intro : forall A B,
  erased_sort B -> erased_pi_sort (TPi A B).
Proof.
  intros A B [j Hj] A' B' Hpi.
  cbn [phi_erase] in Hpi.
  destruct (cjoin_pi_inv _ _ _ _ Hpi) as [_ HB].
  exists j. eapply cjoin_trans; [apply cjoin_sym; exact HB | exact Hj].
Qed.

Lemma erased_pi_sort_sub : forall G T U,
  sub G T U -> erased_pi_sort T -> erased_pi_sort U.
Proof.
  intros G T U H. induction H; intros HT.
  - intros P Q Hpi. apply (HT P Q).
    eapply cjoin_trans; [apply conv_phi_cjoin; exact H | exact Hpi].
  - apply IHsub2, IHsub1, HT.
  - intros P Q Hj. exfalso.
    pose proof (cjoin_hshape_tags_parent _ _ _ _ Hj (hs_sort k) (hs_pi P Q)).
    discriminate.
  - apply erased_pi_sort_intro.
    apply (erased_sort_sub _ _ _ H0).
    apply (HT (phi_erase A) (phi_erase B)). apply cjoin_refl.
  - intros P Q Hj. exfalso.
    assert (HH : hshape (phi_erase (TApp (Carrier E Sf) i)) HMuIApp).
    { cbn [Carrier phi_erase]. constructor. }
    pose proof (cjoin_hshape_tags_parent _ _ _ _ Hj HH (hs_pi P Q)).
    discriminate.
  - intros P Q Hj. exfalso.
    assert (HH : hshape (phi_erase (TApp (TMuS S2) i)) HMuSApp).
    { cbn [phi_erase]. constructor. }
    pose proof (cjoin_hshape_tags_parent _ _ _ _ Hj HH (hs_pi P Q)).
    discriminate.
Qed.

Lemma sub_mu_pi_erased_codomain_sort : forall G IT A B,
  sub G (TPi IT (TSort 0)) (TPi A B) -> erased_sort B.
Proof.
  intros G IT A B HS.
  assert (HI : erased_pi_sort (TPi IT (TSort 0))).
  { apply erased_pi_sort_intro. exists 0. apply cjoin_refl. }
  exact (erased_pi_sort_sub _ _ _ HS HI
    (phi_erase A) (phi_erase B) (cjoin_refl _)).
Qed.

Theorem muapp_sort_erased_proved : forall f a T U h,
  check [] (TApp f a) T -> value (TApp f a) ->
  conv T U -> whd U h -> h = HSort.
Proof.
  intros f a T U h HC HV Hconv HW.
  destruct (check_app_origin _ _ _ HC eq_refl f a eq_refl)
    as [X [HO HS]].
  apply (erased_sort_whd T U h); [|exact Hconv|exact HW].
  apply (erased_sort_sub _ _ _ HS).
  destruct HO as [C HSYN | A B k Hformation HF HA].
  - pose proof (value_app_synth_sort f a C HV HSYN) as ->.
    exists 0. apply cjoin_refl.
  - assert (HFshape : (exists R, f = TMuI R) \/ (exists Sf, f = TMuS Sf)).
    { inversion HV; subst; eauto. }
    destruct (mu_former_checked_erased_pi_origin_luna [] f A B HFshape HF)
      as [IT HPI].
    destruct (sub_mu_pi_erased_codomain_sort _ _ _ _ HPI) as [j Hj].
    exists j. apply erased_sort_cjoin_subst_luna, Hj.
Qed.



End MuApplicationSort.

Theorem muapp_sort : forall f a T U h,
    check [] (TApp f a) T -> value (TApp f a) ->
    conv T U -> whd U h -> h = HSort.
Proof. exact MuApplicationSort.muapp_sort_erased_proved. Qed.

(* ------------------------------------------------------------------ *)
(*  Canonical-form data per class                                      *)
(* ------------------------------------------------------------------ *)

Definition canon (t : term) (h : htag) (U : term) : Prop :=
  match h with
  | HPi => (exists b, t = TLam b) \/ (exists R, t = TMuI R) \/
           (exists Sf, t = TMuS Sf)
  | HSigma => exists a b, t = TPair a b
  | HUnitT => t = TUnit
  | HEnumU => t = TNilE \/ exists tg E, t = TConsE tg E
  | HEnumT =>
      exists tg E0, conv (TEnumT (TConsE tg E0)) U /\
      (t = TEZero \/
       exists n', t = TESucc n' /\ exists E1, check [] n' (TEnumT E1))
  | HIDesc =>
      (exists i, t = TIVar i) \/ t = TI1 \/
      (exists A B, t = TIProd A B) \/ (exists Sd T, t = TIPi Sd T) \/
      (exists Sd T, t = TISig Sd T) \/ (exists E T, t = TIChoice E T)
  | HMuIApp => exists xs, t = TIn xs
  | HMuSApp => exists c xs E0, t = TIn (TPair c xs) /\ check [] c (TEnumT E0)
  | _ => True
  end.

(* a μˢ-typed canonical also serves at μᴵ class (Sig-forget widening) *)
Lemma canon_mus_to_mui : forall t U U',
    canon t HMuSApp U -> canon t HMuIApp U'.
Proof.
  intros t U U' Hc. destruct Hc as [c [xs [E0 [-> _]]]].
  exists (TPair c xs); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(*  Subtyping transport.  A pure-conversion chain keeps the SAME U (so  *)
(*  the U-dependent HEnumT payload survives); the proper subtyping      *)
(*  rules can only land in the four classes below, whose canonical      *)
(*  payloads do not mention U.                                          *)
(* ------------------------------------------------------------------ *)

Lemma sub_transport : forall G A B, sub G A B ->
    forall U h, conv B U -> whd U h ->
    conv A U \/
    ((h = HSort \/ h = HPi \/ h = HMuSApp) /\
     exists U', conv A U' /\ whd U' h) \/
    (h = HMuIApp /\
     exists U', conv A U' /\ (whd U' HMuIApp \/ whd U' HMuSApp)).
Proof.
  intros G A B Hsub. induction Hsub; intros U h HcU Hwhd.
  - (* su_conv *) left. eapply cv_trans; eassumption.
  - (* su_trans *)
    destruct (IHHsub2 U h HcU Hwhd) as
      [HXU | [[Hh [U' [HcU' Hw']]] | [Heq [U' [HcU' Hw']]]]].
    + exact (IHHsub1 U h HXU Hwhd).
    + destruct (IHHsub1 U' h HcU' Hw') as
        [HAU' | [[Hh2 [U'' [HcU'' Hw'']]] | [Heq2 [U'' [HcU'' Hw'']]]]].
      * right; left. split; [exact Hh | exists U'; split; assumption].
      * right; left. split; [exact Hh | exists U''; split; assumption].
      * subst h. destruct Hh as [Hh | [Hh | Hh]]; discriminate Hh.
    + subst h. destruct Hw' as [Hw' | Hw'].
      * destruct (IHHsub1 U' HMuIApp HcU' Hw') as
          [HAU' | [[Hh2 [U'' [HcU'' Hw'']]] | [Heq2 [U'' [HcU'' Hw'']]]]].
        -- right; right. split; [reflexivity |].
           exists U'. split; [exact HAU' | left; exact Hw'].
        -- destruct Hh2 as [Hh2 | [Hh2 | Hh2]]; discriminate Hh2.
        -- right; right. split; [reflexivity |].
           exists U''. split; [exact HcU'' | exact Hw''].
      * destruct (IHHsub1 U' HMuSApp HcU' Hw') as
          [HAU' | [[Hh2 [U'' [HcU'' Hw'']]] | [Heq2 [U'' [HcU'' Hw'']]]]].
        -- right; right. split; [reflexivity |].
           exists U'. split; [exact HAU' | right; exact Hw'].
        -- right; right. split; [reflexivity |].
           exists U''. split; [exact HcU'' | right; exact Hw''].
        -- discriminate Heq2.
  - (* su_sort *)
    assert (HSort = h) as <-.
    { eapply conv_whd; [exact HcU | apply whd_shape; constructor | exact Hwhd]. }
    right; left. split; [left; reflexivity |].
    exists (TSort j). split; [apply cv_refl | apply whd_shape; constructor].
  - (* su_pi *)
    assert (HPi = h) as <-.
    { eapply conv_whd; [exact HcU | apply whd_shape; constructor | exact Hwhd]. }
    right; left. split; [right; left; reflexivity |].
    eexists. split; [apply cv_refl | apply whd_shape; constructor].
  - (* su_forget *)
    assert (HMuIApp = h) as <-.
    { eapply conv_whd;
        [exact HcU | apply whd_shape; unfold Carrier; constructor | exact Hwhd]. }
    right; right. split; [reflexivity |].
    eexists. split; [apply cv_refl | right; apply whd_shape; constructor].
  - (* su_sig *)
    assert (HMuSApp = h) as <-.
    { eapply conv_whd; [exact HcU | apply whd_shape; constructor | exact Hwhd]. }
    right; left. split; [right; right; reflexivity |].
    eexists. split; [apply cv_refl | apply whd_shape; constructor].
Qed.

(* ------------------------------------------------------------------ *)
(*  Canonical forms                                                    *)
(* ------------------------------------------------------------------ *)

(* fix the target class from a literal-headed leaf type *)
Ltac cls C hh Hcc Hww :=
  let E := fresh "Eclass" in
  assert (E : C = hh) by
    (eapply conv_whd; [exact Hcc | apply whd_shape; constructor | exact Hww]);
  subst hh; cbn.

Lemma canon_syn : forall t A, synth [] t A -> value t ->
    forall U h, conv A U -> whd U h -> canon t h U.
Proof.
  intros t A Hsyn Hval U h Hc Hw.
  inversion Hsyn; subst; try (solve [inversion Hval]).
  - (* sy_sort *) cls HSort h Hc Hw. exact I.
  - (* sy_pi *) cls HSort h Hc Hw. exact I.
  - (* sy_sigma *) cls HSort h Hc Hw. exact I.
  - (* sy_app : a stuck mu application *)
    assert (h = HSort) as ->.
    { eapply muapp_sort; [apply check_of_synth; exact Hsyn | exact Hval
                         | exact Hc | exact Hw]. }
    exact I.
  - (* sy_unitT *) cls HSort h Hc Hw. exact I.
  - (* sy_unit *) cls HUnitT h Hc Hw. reflexivity.
  - (* sy_uid *) cls HSort h Hc Hw. exact I.
  - (* sy_enumu *) cls HSort h Hc Hw. exact I.
  - (* sy_tag *) cls HUId h Hc Hw. exact I.
  - (* sy_nile *) cls HEnumU h Hc Hw. left; reflexivity.
  - (* sy_conse *) cls HEnumU h Hc Hw. right; eexists; eexists; reflexivity.
  - (* sy_enumt *) cls HSort h Hc Hw. exact I.
  - (* sy_idesc *) cls HSort h Hc Hw. exact I.
  - (* sy_mui *) cls HPi h Hc Hw. right; left; eexists; reflexivity.
  - (* sy_mus *) cls HPi h Hc Hw. right; right; eexists; reflexivity.
  - (* sy_list *) cls HSort h Hc Hw. exact I.
  - (* sy_lnil *) cls HList h Hc Hw. exact I.
  - (* sy_lcons *) cls HList h Hc Hw. exact I.
Qed.

Lemma canon_main : forall G t T, check G t T -> G = [] -> value t ->
    forall U h, conv T U -> whd U h -> canon t h U.
Proof.
  intros G t T Hck. induction Hck; intros HG Hval U h Hc Hw; subst.
  - (* ch_conv *)
    match goal with
    | Hs : synth [] ?t0 ?A0, Hcv : conv ?A0 ?B0 |- _ =>
        eapply canon_syn;
        [exact Hs | exact Hval
        | eapply cv_trans; [exact Hcv | exact Hc] | exact Hw]
    end.
  - (* ch_sub *)
    match goal with
    | Hsub : sub [] ?A0 ?B0 |- _ =>
        destruct (sub_transport [] A0 B0 Hsub U h Hc Hw) as
          [HcAU | [[Hh [U' [HcU' Hw']]] | [Heq [U' [HcU' Hw']]]]];
        [ eapply IHHck; [reflexivity | exact Hval | exact HcAU | exact Hw]
        | destruct Hh as [-> | [-> | ->]];
          (assert (K : canon _ _ U') by
             (eapply IHHck; [reflexivity | exact Hval | exact HcU' | exact Hw']);
           exact K)
        | subst h; destruct Hw' as [Hw' | Hw'];
          [ assert (K : canon _ HMuIApp U') by
              (eapply IHHck; [reflexivity | exact Hval | exact HcU' | exact Hw']);
            exact K
          | assert (K : canon _ HMuSApp U') by
              (eapply IHHck; [reflexivity | exact Hval | exact HcU' | exact Hw']);
            exact (canon_mus_to_mui _ U' U K) ] ]
    end.
  - (* ch_expand *)
    match goal with
    | Hcv : conv ?A0 ?B0 |- _ =>
        apply IHHck;
        [reflexivity | exact Hval
        | eapply cv_trans; [eapply cv_sym; exact Hcv | exact Hc] | exact Hw]
    end.
  - (* ch_lam *) cls HPi h Hc Hw. left; eexists; reflexivity.
  - (* ch_pair *) cls HSigma h Hc Hw. eexists; eexists; reflexivity.
  - (* ch_app : a stuck μ application *)
    assert (h = HSort) as ->.
    { eapply muapp_sort;
        [eapply ch_app; eassumption | exact Hval | exact Hc | exact Hw]. }
    exact I.
  - (* ch_fst *) inversion Hval.
  - (* ch_snd *) inversion Hval.
  - (* ch_ezero *) cls HEnumT h Hc Hw.
    do 2 eexists. split; [exact Hc | left; reflexivity].
  - (* ch_esucc *) cls HEnumT h Hc Hw.
    do 2 eexists. split; [exact Hc |].
    right. eexists. split; [reflexivity |].
    match goal with Hn : check [] ?n0 (TEnumT ?E0) |- _ =>
      exists E0; exact Hn end.
  - (* ch_ivar *) cls HIDesc h Hc Hw. left; eexists; reflexivity.
  - (* ch_i1 *) cls HIDesc h Hc Hw. right; left; reflexivity.
  - (* ch_iprod *) cls HIDesc h Hc Hw.
    right; right; left; eexists; eexists; reflexivity.
  - (* ch_ipi *) cls HIDesc h Hc Hw.
    right; right; right; left; eexists; eexists; reflexivity.
  - (* ch_isig *) cls HIDesc h Hc Hw.
    right; right; right; right; left; eexists; eexists; reflexivity.
  - (* ch_ichoice *) cls HIDesc h Hc Hw.
    right; right; right; right; right; eexists; eexists; reflexivity.
  - (* ch_in_mui *) cls HMuIApp h Hc Hw. eexists; reflexivity.
  - (* ch_in_sig *) cls HMuSApp h Hc Hw.
    match goal with Hc0 : check [] ?c0 (Label ?E0) |- _ =>
      eexists; eexists; exists E0; split; [reflexivity | exact Hc0] end.
Qed.

(* ------------------------------------------------------------------ *)
(*  Typing inversion for eliminator shapes (empty context)             *)
(* ------------------------------------------------------------------ *)

Lemma inv_var : forall G t T, check G t T -> G = [] ->
    forall n, t = TVar n -> False.
Proof.
  intros G t T Hck. induction Hck; intros HG n0 Heq; subst; try discriminate.
  - match goal with Hs : synth [] (TVar _) _ |- _ =>
      inversion Hs; subst;
      match goal with Hne : nth_error [] ?m = Some _ |- _ =>
        destruct m; discriminate Hne end
    end.
  - exact (IHHck eq_refl n0 eq_refl).
  - exact (IHHck eq_refl n0 eq_refl).
Qed.

Ltac syn_app_emit :=
  match goal with Hs : synth [] (TApp _ _) _ |- _ =>
    inversion Hs; subst;
    match goal with
      Hsf : synth [] ?f0 ?C, Hev : eval ?C (TPi ?A1 ?B1) |- _ =>
        exists C; split;
        [apply check_of_synth; exact Hsf
        | exists (TPi A1 B1); split; [exact Hev | constructor]]
    end
  end.

Lemma inv_app : forall G t T, check G t T -> G = [] ->
    forall f a, t = TApp f a ->
    exists T', check [] f T' /\ whd T' HPi.
Proof.
  intros G t T Hck. induction Hck; intros HG f0 a0 Heq; subst; try discriminate.
  - syn_app_emit.
  - exact (IHHck eq_refl f0 a0 eq_refl).
  - exact (IHHck eq_refl f0 a0 eq_refl).
  - (* ch_app *)
    match goal with Heq2 : TApp _ _ = TApp _ _ |- _ =>
      inversion Heq2; subst end.
    match goal with Hf : check [] ?f1 (TPi ?A1 ?B1) |- _ =>
      exists (TPi A1 B1); split;
      [exact Hf | apply whd_shape; constructor]
    end.
Qed.

Ltac syn_proj_emit :=
  match goal with Hs : synth [] (_ _) _ |- _ =>
    inversion Hs; subst;
    match goal with
      Hsp : synth [] ?p0 ?C, Hev : eval ?C (TSigma ?A1 ?B1) |- _ =>
        exists C; split;
        [apply check_of_synth; exact Hsp
        | exists (TSigma A1 B1); split; [exact Hev | constructor]]
    end
  end.

Lemma inv_fst : forall G t T, check G t T -> G = [] ->
    forall p, t = TFst p ->
    exists T', check [] p T' /\ whd T' HSigma.
Proof.
  intros G t T Hck. induction Hck; intros HG p0 Heq; subst; try discriminate.
  - syn_proj_emit.
  - exact (IHHck eq_refl p0 eq_refl).
  - exact (IHHck eq_refl p0 eq_refl).
  - match goal with Heq2 : TFst _ = TFst _ |- _ => inversion Heq2; subst end.
    match goal with Hp : check [] ?p1 (TSigma ?A1 ?B1) |- _ =>
      exists (TSigma A1 B1); split;
      [exact Hp | apply whd_shape; constructor]
    end.
Qed.

Lemma inv_snd : forall G t T, check G t T -> G = [] ->
    forall p, t = TSnd p ->
    exists T', check [] p T' /\ whd T' HSigma.
Proof.
  intros G t T Hck. induction Hck; intros HG p0 Heq; subst; try discriminate.
  - syn_proj_emit.
  - exact (IHHck eq_refl p0 eq_refl).
  - exact (IHHck eq_refl p0 eq_refl).
  - match goal with Heq2 : TSnd _ = TSnd _ |- _ => inversion Heq2; subst end.
    match goal with Hp : check [] ?p1 (TSigma ?A1 ?B1) |- _ =>
      exists (TSigma A1 B1); split;
      [exact Hp | apply whd_shape; constructor]
    end.
Qed.

Ltac syn_prem_emit :=
  match goal with Hs : synth [] _ _ |- _ =>
    inversion Hs; subst; repeat split; try eassumption;
    try (eexists; eassumption)
  end.

Lemma inv_epi : forall G t T, check G t T -> G = [] ->
    forall E P, t = TEPi E P -> check [] E TEnumU.
Proof.
  intros G t T Hck. induction Hck; intros HG E0 P0 Heq; subst; try discriminate.
  - syn_prem_emit.
  - exact (IHHck eq_refl E0 P0 eq_refl).
  - exact (IHHck eq_refl E0 P0 eq_refl).
Qed.

Lemma inv_switch : forall G t T, check G t T -> G = [] ->
    forall E P p e, t = TSwitch E P p e ->
    check [] E TEnumU /\ check [] p (TEPi E P) /\ check [] e (TEnumT E).
Proof.
  intros G t T Hck. induction Hck; intros HG E0 P0 p0 e0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - exact (IHHck eq_refl E0 P0 p0 e0 eq_refl).
  - exact (IHHck eq_refl E0 P0 p0 e0 eq_refl).
Qed.

Lemma inv_interp : forall G t T, check G t T -> G = [] ->
    forall D X, t = TInterp D X -> exists IT, check [] D (TIDesc IT).
Proof.
  intros G t T Hck. induction Hck; intros HG D0 X0 Heq; subst; try discriminate.
  - syn_prem_emit.
  - exact (IHHck eq_refl D0 X0 eq_refl).
  - exact (IHHck eq_refl D0 X0 eq_refl).
Qed.

Lemma inv_iall : forall G t T, check G t T -> G = [] ->
    forall D X xs P, t = TIAll D X xs P ->
    (exists IT, check [] D (TIDesc IT)) /\ check [] xs (TInterp D X).
Proof.
  intros G t T Hck. induction Hck; intros HG D0 X0 xs0 P0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - exact (IHHck eq_refl D0 X0 xs0 P0 eq_refl).
  - exact (IHHck eq_refl D0 X0 xs0 P0 eq_refl).
Qed.

Lemma inv_hyps : forall G t T, check G t T -> G = [] ->
    forall D X P h xs, t = THyps D X P h xs ->
    (exists IT, check [] D (TIDesc IT)) /\ check [] xs (TInterp D X).
Proof.
  intros G t T Hck. induction Hck; intros HG D0 X0 P0 h0 xs0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - exact (IHHck eq_refl D0 X0 P0 h0 xs0 eq_refl).
  - exact (IHHck eq_refl D0 X0 P0 h0 xs0 eq_refl).
Qed.

Lemma inv_ind : forall G t T, check G t T -> G = [] ->
    forall R P stp i x, t = TInd R P stp i x ->
    check [] x (TApp (TMuI R) i).
Proof.
  intros G t T Hck. induction Hck; intros HG R0 P0 stp0 i0 x0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - exact (IHHck eq_refl R0 P0 stp0 i0 x0 eq_refl).
  - exact (IHHck eq_refl R0 P0 stp0 i0 x0 eq_refl).
Qed.

Lemma inv_case : forall G t T, check G t T -> G = [] ->
    forall M Q bs, t = TCase M Q bs ->
    exists Sf i IT E Phi,
      check [] M (TApp (SigMu E Sf) i) /\
      check [] IT (TSort 0) /\ check [] E TEnumU /\
      check [] Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) /\
      check [] i IT /\
      eval (labels (TApp Sf i)) Phi /\
      covers (map fst bs) Phi /\
      check_branches [] Sf i E Q bs.
Proof.
  intros G t T Hck. induction Hck; intros HG M0 Q0 bs0 Heq; subst;
    try discriminate.
  - match goal with Hs : synth [] (TCase _ _ _) _ |- _ =>
      inversion Hs; subst;
      do 5 eexists; repeat split; eassumption
    end.
  - exact (IHHck eq_refl M0 Q0 bs0 eq_refl).
  - exact (IHHck eq_refl M0 Q0 bs0 eq_refl).
Qed.

Lemma cb_labels : forall G Sf i E Q bs,
    check_branches G Sf i E Q bs ->
    Forall (fun cb => check G (fst cb) (TEnumT E)) bs.
Proof.
  intros G Sf i E Q bs Hcb. induction Hcb; constructor; cbn; auto.
Qed.

(* ------------------------------------------------------------------ *)
(*  Auxiliaries for the case redex                                     *)
(* ------------------------------------------------------------------ *)

(* evaluation cannot change a canonical scrutinee tag *)
Lemma eval_in_tag : forall n c xs V, enum_pos c n ->
    eval (TIn (TPair c xs)) V -> exists xs', V = TIn (TPair c xs').
Proof.
  intros n c xs V Hp Hev. remember (TIn (TPair c xs)) as t0 eqn:Ht.
  revert c xs Hp Ht.
  induction Hev as [t | t u v Hst Hev IH]; intros c xs Hp Ht; subst.
  - eexists; reflexivity.
  - inversion Hst; subst.
    match goal with Hpp : step (TPair _ _) _ |- _ =>
      inversion Hpp; subst end.
    + match goal with Hc : step c ?c' |- _ =>
        exfalso; exact (pos_step_normal c n Hp c' Hc) end.
    + eapply IH; [exact Hp | reflexivity].
Qed.

Lemma spine_mem_pre : forall L Phi a,
    eval L Phi -> spine_mem a Phi -> spine_mem a L.
Proof.
  intros L Phi a Hev Hm. inversion Hm; subst.
  - eapply sm_here; [eapply eval_trans; eassumption | assumption].
  - eapply sm_there; [eapply eval_trans; eassumption | assumption].
Qed.

Lemma covers_pre : forall L Phi Psi,
    eval L Phi -> covers Psi Phi -> covers Psi L.
Proof.
  intros L Phi Psi Hev Hc. inversion Hc; subst.
  - eapply cov_nil. eapply eval_trans; eassumption.
  - eapply cov_cons; [eapply eval_trans; eassumption | assumption | assumption].
Qed.

Lemma forall2_in_l :
  forall (A B : Type) (R : A -> B -> Prop) (l : list A) (ns : list B) x,
    Forall2 R l ns -> In x l -> exists y, In y ns /\ R x y.
Proof.
  intros A B R l ns x HF. induction HF; intros Hin.
  - destruct Hin.
  - destruct Hin as [-> | Hin].
    + exists y. split; [left; reflexivity | assumption].
    + destruct (IHHF Hin) as [y0 [Hy0 HR]].
      exists y0. split; [right; assumption | assumption].
Qed.

Lemma forall_ex_forall2 : forall (bs : list (term * term)),
    Forall (fun cb => exists m, enum_pos (fst cb) m) bs ->
    exists ns, Forall2 (fun cb m => enum_pos (fst cb) m) bs ns.
Proof.
  induction bs as [|cb bs IH]; intros HF.
  - exists []. constructor.
  - inversion HF as [|? ? Hhd Htl]; subst.
    destruct Hhd as [m Hm]. destruct (IH Htl) as [ns Hns].
    exists (m :: ns). constructor; assumption.
Qed.

(* either some clause label steps (in place), or all are canonical *)
Lemma labels_walk : forall bs : list (term * term),
    Forall (fun cb => (exists m, enum_pos (fst cb) m) \/
                      (exists c', step (fst cb) c')) bs ->
    (exists bs1 c b bs2 c', bs = bs1 ++ (c, b) :: bs2 /\ step c c') \/
    Forall (fun cb => exists m, enum_pos (fst cb) m) bs.
Proof.
  induction bs as [|[c b] bs IH]; intros HF.
  - right; constructor.
  - inversion HF as [|? ? Hhd Htl]; subst. cbn in Hhd.
    destruct Hhd as [Hp | [c' Hst]].
    + destruct (IH Htl) as [[bs1 [c0 [b0 [bs2 [c0' [Heq Hst0]]]]]] | Hall].
      * left. exists ((c, b) :: bs1), c0, b0, bs2, c0'.
        cbn. rewrite Heq. auto.
      * right. constructor; [exact Hp | exact Hall].
    + left. exists [], c, b, bs, c'. cbn. auto.
Qed.

(* the first clause whose label sits at position n, with the first-match
   prefix condition st_case requires *)
Lemma find_first : forall (l : list (term * term)) (ns : list nat) n,
    Forall2 (fun cb m => enum_pos (fst cb) m) l ns ->
    In n ns ->
    exists k c b,
      nth_error l k = Some (c, b) /\ enum_pos c n /\
      (forall j cj bj, j < k -> nth_error l j = Some (cj, bj) ->
          exists nj, enum_pos cj nj /\ nj <> n).
Proof.
  intros l ns n HF. revert n.
  induction HF as [|[c b] m l' ns' Hp HF IH]; intros n Hin.
  - destruct Hin.
  - cbn in Hp. destruct (Nat.eq_dec m n) as [-> | Hne].
    + exists 0, c, b. cbn. repeat split; auto.
      intros j cj bj Hlt _. lia.
    + destruct Hin as [-> | Hin]; [congruence |].
      destruct (IH n Hin) as [k [c0 [b0 [Hnth [Hp0 Hpre]]]]].
      exists (S k), c0, b0. cbn. repeat split; auto.
      intros j cj bj Hlt Hnthj. destruct j as [|j'].
      * cbn in Hnthj. inversion Hnthj; subst. exists m. split; auto.
      * cbn in Hnthj. eapply (Hpre j' cj bj); [lia | exact Hnthj].
Qed.

(* ------------------------------------------------------------------ *)
(*  Progress                                                           *)
(* ------------------------------------------------------------------ *)


(* Checked signature-transport component: SignatureLemmas. *)
Module SignatureLemmas.
(* Supporting lemmas for the remaining signature canonical-forms proof.
   These do not assert canonical_forms_sig or change the typing rules.
   Each exported result below is audited without axioms. *)

Import ListNotations TypeRulesCore _tmp_epstep
  _work_mixed_closure _work_cjoin
  _work_cstep_invariants _work_conv_whd_pos
  _luna_phi_erase_shapes MuApplicationSort.

(* _luna_repair_sigma_join *)
Lemma pstep_sigma_inv_luna : forall A B u, pstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_sigma_inv_luna : forall A B u, rtc pstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TSigma A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_sigma_inv_luna A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_sigma_inv_luna : forall A B u, epstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_sigma_inv_luna : forall A B u, rtc epstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TSigma A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_sigma_inv_luna A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_sigma_inv_luna : forall A B u, cstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_sigma_inv_luna _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_sigma_inv_luna _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_sigma_inv_luna : forall A B u, rtc cstep (TSigma A B) u ->
    exists A' B', u = TSigma A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TSigma A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_sigma_inv_luna A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_sigma_inv_luna : forall A1 B1 A2 B2,
    cjoin (TSigma A1 B1) (TSigma A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_sigma_inv_luna _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_sigma_inv_luna _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.

(* A subtyping chain whose two endpoints are syntactic Sigma types can only
   use conversion at that head; the proper subtyping rules have other heads. *)
Lemma sub_sigma_endpoints_conv : forall G A B A' B',
    sub G (TSigma A B) (TSigma A' B') ->
    conv (TSigma A B) (TSigma A' B').
Proof.
  intros G A B A' B' Hsub.
  destruct (sub_transport G (TSigma A B) (TSigma A' B') Hsub
      (TSigma A' B') HSigma (cv_refl (TSigma A' B'))
      (whd_shape (TSigma A' B') HSigma (hs_sigma A' B')))
    as [Hconv | [[Htag _] | [Htag _]]].
  - exact Hconv.
  - destruct Htag as [Htag | [Htag | Htag]]; discriminate Htag.
  - discriminate Htag.
Qed.

Lemma pair_origin_aux : forall G t T, check G t T -> forall a b, t = TPair a b ->
    exists A B, check G a A /\ check G b (subst a 0 B) /\
      sub G (TSigma A B) T.
Proof.
  intros G t T HC; induction HC; intros aa bb Eqpair; try discriminate; inversion Eqpair; subst.
  - inversion H.
  - destruct (IHHC aa bb eq_refl) as [A0 [B0 [Ha [Hb HT]]]].
    exists A0, B0; repeat split; try assumption.
    eapply su_trans; eassumption.
  - destruct (IHHC aa bb eq_refl) as [A0 [B0 [Ha [Hb HT]]]].
    exists A0, B0; repeat split; try assumption.
    eapply su_trans; [exact HT | apply su_conv, cv_sym; exact H].
  - exists A, B; repeat split; eauto using su_conv, cv_refl.
Qed.

Lemma pair_origin : forall G a b T,
    check G (TPair a b) T ->
    exists A B, check G a A /\ check G b (subst a 0 B) /\
      sub G (TSigma A B) T.
Proof. intros; eapply pair_origin_aux; eauto. Qed.

(* _luna_repair_in_sig_origin *)
Lemma in_pair_origin_aux : forall G t T, check G t T -> forall c xs,
    t = TIn (TPair c xs) ->
    (exists R i IT,
       check G IT (TSort 0) /\
       check G R (TPi IT (TIDesc (lift 1 0 IT))) /\
       check G i IT /\
       check G (TPair c xs) (TInterp (TApp R i) (TMuI R)) /\
       sub G (TApp (TMuI R) i) T) \/
    (exists Sf i IT E Phi,
       check G IT (TSort 0) /\ check G E TEnumU /\
       check G Sf (TPi IT (Sig (lift 1 0 IT) (lift 1 0 E))) /\
       check G i IT /\ check G c (Label E) /\
       eval (labels (TApp Sf i)) Phi /\ spine_mem c Phi /\
       check G xs (TInterp (TApp (branches (TApp Sf i)) c) (Carrier E Sf)) /\
       sub G (TApp (SigMu E Sf) i) T).
Proof.
  intros G t T HC; induction HC; intros c0 xs0 Eq; try discriminate; inversion Eq; subst.
  - inversion H.
  - destruct (IHHC c0 xs0 eq_refl) as [K | K].
    + destruct K as [R [i [IT [HIT [HR [Hi [Hx Hty]]]]]]].
      left; exists R, i, IT; repeat split; try assumption.
      eapply su_trans; eassumption.
    + destruct K as [Sf [i [IT [E [Phi [HIT [HE [HSf [Hi [Hc [Hl [Hm [Hx Hty]]]]]]]]]]]]].
      right; exists Sf, i, IT, E, Phi; repeat split; try assumption.
      eapply su_trans; eassumption.
  - destruct (IHHC c0 xs0 eq_refl) as [K | K].
    + destruct K as [R [i [IT [HIT [HR [Hi [Hx Hty]]]]]]].
      left; exists R, i, IT; repeat split; try assumption.
      eapply su_trans; [exact Hty | apply su_conv, cv_sym; exact H].
    + destruct K as [Sf [i [IT [E [Phi [HIT [HE [HSf [Hi [Hc [Hl [Hm [Hx Hty]]]]]]]]]]]]].
      right; exists Sf, i, IT, E, Phi; repeat split; try assumption.
      eapply su_trans; [exact Hty | apply su_conv, cv_sym; exact H].
  - left; exists R, i, IT; repeat split; eauto using su_conv, cv_refl.
  - right; exists Sf, i, IT, E, Phi; repeat split; eauto using su_conv, cv_refl.
Qed.

Lemma in_pair_mus_origin : forall c xs E Sf i,
    check [] (TIn (TPair c xs)) (TApp (SigMu E Sf) i) ->
    exists S0 i0 IT0 E0 Phi0,
      check [] IT0 (TSort 0) /\ check [] E0 TEnumU /\
      check [] S0 (TPi IT0 (Sig (lift 1 0 IT0) (lift 1 0 E0))) /\
      check [] i0 IT0 /\ check [] c (Label E0) /\
      eval (labels (TApp S0 i0)) Phi0 /\ spine_mem c Phi0 /\
      check [] xs (TInterp (TApp (branches (TApp S0 i0)) c)
        (Carrier E0 S0)) /\
      sub [] (TApp (SigMu E0 S0) i0) (TApp (SigMu E Sf) i).
Proof.
  intros c xs E Sf i H.
  destruct (in_pair_origin_aux [] (TIn (TPair c xs)) (TApp (SigMu E Sf) i)
              H c xs eq_refl) as [KM | KS].
  - destruct KM as [R [i0 [IT0 [HIT0 [HR [Hi0 [Hx Hsub]]]]]]].
    exfalso.
    destruct (sub_transport _ _ _ Hsub _ _ (cv_refl _)
      (whd_shape _ _ (hs_musapp (TPair E Sf) i))) as
      [Hconv | [[Htag [U [Hconv HU]]] | [Htag [U [Hconv HU]]]]].
    + pose proof (conv_whd_proved _ _ _ _ Hconv
        (whd_shape _ _ (hs_muiapp R i0))
        (whd_shape _ _ (hs_musapp (TPair E Sf) i))) as K. discriminate K.
    + destruct Htag as [Htag | [Htag | Htag]]; try discriminate Htag.
      pose proof (conv_whd_proved _ _ _ _ Hconv
        (whd_shape _ _ (hs_muiapp R i0)) HU) as K. discriminate K.
    + discriminate Htag.
  - destruct KS as [S0 [i0 [IT0 [E0 [Phi0
      [HIT0 [HE0 [HS0 [Hi0 [Hc [HL [Hm [Hx Hconv]]]]]]]]]]]]].
    exists S0, i0, IT0, E0, Phi0.
    repeat split; assumption.
Qed.

(* _luna_repair_spine *)
(* This is the direct signature-transport fact needed by [su_sig]. *)
Lemma luna_spine_mem_conv : forall a b L,
    conv a b -> spine_mem b L -> spine_mem a L.
Proof.
  intros a b L Hab H. induction H.
  - eapply sm_here; eauto using cv_trans.
  - eapply sm_there; eauto using cv_trans.
Qed.

Lemma luna_neutral_pstep : forall n, neutral n -> forall u,
    pstep n u -> neutral u.
Proof.
  intros n Hn. induction Hn; intros u Hp; inversion Hp; subst;
    eauto using neutral; try assumption.
  all: repeat match goal with
    | H : neutral (TLam _) |- _ => inversion H
    | H : neutral (TPair _ _) |- _ => inversion H
    | H : neutral (TIn _) |- _ => inversion H
    | H : neutral TEZero |- _ => inversion H
    | H : neutral (TESucc _) |- _ => inversion H
    end; eauto using neutral.
Qed.

Lemma luna_neutral_psteps : forall n, neutral n -> forall u,
    rtc pstep n u -> neutral u.
Proof.
  intros n Hn u H. revert Hn.
  induction H as [x | x y z Hxy Hyz IH]; intros Hn.
  - exact Hn.
  - apply IH. eapply luna_neutral_pstep; eassumption.
Qed.

Lemma luna_no_pjoin_lcons_neutral : forall A a l n,
    neutral n -> ~ pjoin (TLCons A a l) n.
Proof.
  intros A a l n Hn [w [Hl Hn']].
  destruct (psteps_lcons_inv _ _ _ _ Hl)
    as [A' [a' [l' [Hw _]]]].
  pose proof (luna_neutral_psteps n Hn w Hn') as Hnw.
  rewrite Hw in Hnw. inversion Hnw.
Qed.

(* _luna_repair_empty_enum_sub *)
Definition erased_empty_enum (T : term) : Prop :=
  cjoin (phi_erase T) (TEnumT TNilE).

Lemma luna_cjoin_hshape_tag : forall t u h1 h2,
    cjoin t u -> hshape t h1 -> hshape u h2 -> h1 = h2.
Proof.
  intros t u h1 h2 [w [Ht Hu]] Htshape Hushape.
  pose proof (rtc_cstep_hshape _ _ Ht h1 Htshape) as Hw1.
  pose proof (rtc_cstep_hshape _ _ Hu h2 Hushape) as Hw2.
  eapply hshape_tag_unique; eassumption.
Qed.

Lemma luna_phi_erase_sort : forall k, hshape (phi_erase (TSort k)) HSort.
Proof. intros; cbn; constructor. Qed.

Lemma luna_phi_erase_pi : forall A B,
    hshape (phi_erase (TPi A B)) HPi.
Proof. intros; cbn; constructor. Qed.

Lemma luna_phi_erase_carrier : forall E Sf i,
    hshape (phi_erase (TApp (Carrier E Sf) i)) HMuIApp.
Proof. intros; cbn [phi_erase Carrier]; constructor. Qed.

Lemma luna_phi_erase_musapp : forall Sf i,
    hshape (phi_erase (TApp (TMuS Sf) i)) HMuSApp.
Proof. intros; cbn; constructor. Qed.

Lemma erased_empty_enum_sub_back : forall G A B,
    sub G A B -> erased_empty_enum B -> erased_empty_enum A.
Proof.
  intros G A B Hsub. induction Hsub; intro Hempty.
  - unfold erased_empty_enum in *. eapply cjoin_trans;
      [apply conv_phi_cjoin; exact H | exact Hempty].
  - exact (IHHsub1 (IHHsub2 Hempty)).
  - unfold erased_empty_enum in Hempty. exfalso.
    assert (Heq : HSort = HEnumT).
    { eapply (luna_cjoin_hshape_tag _ _ _ _ Hempty).
      - apply luna_phi_erase_sort.
      - constructor. }
    discriminate Heq.
  - unfold erased_empty_enum in Hempty. exfalso.
    assert (Heq : HPi = HEnumT).
    { eapply (luna_cjoin_hshape_tag _ _ _ _ Hempty).
      - apply luna_phi_erase_pi.
      - constructor. }
    discriminate Heq.
  - unfold erased_empty_enum in Hempty. exfalso.
    assert (Heq : HMuIApp = HEnumT).
    { eapply (luna_cjoin_hshape_tag _ _ _ _ Hempty).
      - apply luna_phi_erase_carrier.
      - constructor. }
    discriminate Heq.
  - unfold erased_empty_enum in Hempty. exfalso.
    assert (Heq : HMuSApp = HEnumT).
    { eapply (luna_cjoin_hshape_tag _ _ _ _ Hempty).
      - apply luna_phi_erase_musapp.
      - constructor. }
    discriminate Heq.
Qed.

(* _luna_repair_empty_enum_value *)
Lemma cjoin_erased_sort_empty_enum_luna : forall k,
    cjoin (phi_erase (TSort k)) (TEnumT TNilE) -> False.
Proof.
  intros k H.
  pose proof (cjoin_hshape_tags_parent _ _ _ _ H
    (phi_erase_hshape_luna (TSort k) HSort (hs_sort k)) (hs_enumt TNilE)) as E.
  discriminate E.
Qed.

Lemma erased_enum_clash_luna : forall T h,
    cjoin (phi_erase T) (TEnumT TNilE) ->
    hshape (phi_erase T) h -> h <> HEnumT -> False.
Proof.
  intros T h HJ HH Hneq.
  pose proof (cjoin_hshape_tags_parent _ _ _ _ HJ HH
    (hs_enumt TNilE)) as E.
  exact (Hneq E).
Qed.

Lemma no_value_empty_enum_luna : forall v T,
    value v -> check [] v T -> conv T (TEnumT TNilE) -> False.
Proof.
  intros v T Hv Hcheck Hconv.
  pose proof (canon_main [] v T Hcheck eq_refl Hv
    (TEnumT TNilE) HEnumT Hconv
    (whd_shape _ _ (hs_enumt TNilE))) as Hcanon.
  cbn in Hcanon.
  destruct Hcanon as [tg [E0 [Hbad Hshape]]].
  exact (conv_enumt_cons_nil_absurd tg E0 Hbad).
Qed.

Lemma erased_empty_synth_value : forall t T,
    synth [] t T -> value t ->
    cjoin (phi_erase T) (TEnumT TNilE) -> False.
Proof.
  intros t T Hsyn Hv HJ.
  inversion Hsyn; subst; try solve [inversion Hv].
  all: try solve [
    eapply erased_enum_clash_luna; [exact HJ | cbn [phi_erase]; constructor | discriminate] ].
  all: try match goal with
  | HS : synth [] (TApp ?f ?a) ?C |- _ =>
      pose proof (value_app_synth_sort f a C Hv HS) as ->;
      eapply cjoin_erased_sort_empty_enum_luna; exact HJ
  end.
  pose proof (value_app_synth_sort _ _ _ Hv Hsyn) as Hsort.
  rewrite Hsort in HJ.
  exact (cjoin_erased_sort_empty_enum_luna 0 HJ).
Qed.

(* _luna_repair_empty_enum_check *)
Lemma luna_empty_enum_cons_nil : forall tg E,
    cjoin (TEnumT (TConsE tg E)) (TEnumT TNilE) -> False.
Proof.
  intros tg E [w [HL HR]].
  destruct (rtc_cstep_enumt_inv _ _ HL) as [L [EL HL']].
  destruct (rtc_cstep_enumt_inv _ _ HR) as [R [ER HR']].
  rewrite EL in ER. inversion ER; subst R.
  pose proof (rtc_cstep_hshape _ _ HL' HConsE (hs_conse _ _)) as HC2.
  pose proof (rtc_cstep_hshape _ _ HR' HNilE hs_nile) as HN2.
  pose proof (hshape_tag_unique _ _ _ HC2 HN2). discriminate.
Qed.

Lemma luna_check_app_erased_sort : forall f a T,
    check [] (TApp f a) T -> value (TApp f a) ->
    erased_sort T.
Proof.
  intros f a T HC HV.
  destruct (check_app_origin [] (TApp f a) T HC eq_refl f a eq_refl)
    as [X [HO HS]].
  apply (erased_sort_sub _ _ _ HS).
  destruct HO as [C HSYN | A B k Hformation HF HA].
  - pose proof (value_app_synth_sort f a C HV HSYN) as ->.
    exists 0. apply cjoin_refl.
  - assert (HFshape : (exists R, f = TMuI R) \/ (exists Sf, f = TMuS Sf)).
    { inversion HV; subst; eauto. }
    destruct (mu_former_checked_erased_pi_origin_luna [] f A B HFshape HF)
      as [IT HPI].
    destruct (sub_mu_pi_erased_codomain_sort _ _ _ _ HPI) as [j Hj].
    exists j. apply erased_sort_cjoin_subst_luna, Hj.
Qed.

Lemma erased_empty_check_value_luna : forall G t T,
    check G t T -> G = [] -> value t -> erased_empty_enum T -> False.
Proof.
  intros G t T Hcheck.
  induction Hcheck; intros HG Hv Hempty; subst.
  all: try solve [inversion Hv].
  all: try solve [eapply erased_enum_clash_luna;
    [exact Hempty | cbn [phi_erase]; constructor | discriminate]].
  all: try solve [eapply luna_empty_enum_cons_nil; exact Hempty].
  - eapply erased_empty_synth_value; [exact H | exact Hv |].
    eapply cjoin_trans; [apply conv_phi_cjoin; exact H0 | exact Hempty].
  - apply (IHHcheck eq_refl Hv).
    exact (erased_empty_enum_sub_back [] A B H Hempty).
  - apply (IHHcheck eq_refl Hv).
    eapply cjoin_trans; [apply conv_phi_cjoin, cv_sym; exact H | exact Hempty].
  - assert (HCapp : check [] (TApp f a) (subst a 0 B)).
    { eapply ch_app; eassumption. }
    destruct (luna_check_app_erased_sort f a (subst a 0 B) HCapp Hv)
      as [j Hj].
    assert (HJ : cjoin (TSort j) (TEnumT TNilE)).
    { eapply cjoin_trans; [apply cjoin_sym; exact Hj | exact Hempty]. }
    pose proof (luna_cjoin_hshape_tag _ _ _ _ HJ
      (hs_sort j) (hs_enumt TNilE)) as K.
    discriminate K.
Qed.

(* _parent_repair_dead_choice *)
Lemma eval_interp_description_parent : forall D D' X,
  eval D D' -> eval (TInterp D X) (TInterp D' X).
Proof.
  intros D D' X HE. induction HE.
  - apply ev_refl.
  - eapply ev_step; [apply st_interp1; exact H | exact IHHE].
Qed.

Lemma empty_choice_domain_parent : forall a b D X E F,
  check [] (TPair a b) (TInterp D X) ->
  eval D (TIChoice E F) -> eval E TNilE ->
  exists A, check [] a A /\
    cjoin (phi_erase A) (TEnumT TNilE).
Proof.
  intros a b D X E F HC HD HE.
  destruct (pair_origin _ _ _ _ HC) as [A [B [HA [HB Hsub]]]].
  exists A. split; [exact HA |].
  assert (HI : conv (TInterp D X)
    (TSigma (TEnumT E)
      (TInterp (TApp (lift 1 0 F) (TVar 0)) (lift 1 0 X)))).
  { eapply cv_trans.
    - apply cv_interp; [apply conv_of_eval; exact HD | apply cv_refl].
    - apply cv_step, st_interp_choice. }
  assert (Hsigsub : sub [] (TSigma A B)
      (TSigma (TEnumT E)
        (TInterp (TApp (lift 1 0 F) (TVar 0)) (lift 1 0 X)))).
  { eapply su_trans; [exact Hsub | apply su_conv; exact HI]. }
  pose proof (conv_phi_cjoin _ _
    (sub_sigma_endpoints_conv _ _ _ _ _ Hsigsub)) as HJ.
  cbn [phi_erase] in HJ.
  destruct (cjoin_sigma_inv_luna _ _ _ _ HJ) as [HJdom _].
  eapply cjoin_trans; [exact HJdom |].
  change (cjoin (phi_erase (TEnumT E)) (phi_erase (TEnumT TNilE))).
  apply conv_phi_cjoin, cv_enumt, conv_of_eval, HE.
Qed.

Lemma empty_choice_pair_parent : forall xs D X E F,
  check [] xs (TInterp D X) -> value xs ->
  eval D (TIChoice E F) -> exists a b, xs = TPair a b.
Proof.
  intros xs D X E F HC HV HD.
  assert (HW : whd (TInterp D X) HSigma).
  { eexists. split.
    - eapply eval_trans.
      + apply eval_interp_description_parent; exact HD.
      + eapply ev_step; [apply st_interp_choice | apply ev_refl].
    - constructor. }
  exact (canon_main [] xs _ HC eq_refl HV _ HSigma (cv_refl _) HW).
Qed.

Lemma dead_choice_nil_progress_parent : forall xs D X E F,
  check [] xs (TInterp D X) -> value xs ->
  eval D (TIChoice E F) -> eval E TNilE ->
  (forall a b A, xs = TPair a b -> check [] a A ->
     value a \/ exists a', step a a') ->
  exists xs', step xs xs'.
Proof.
  intros xs D X E F HC HV HD HE IH.
  destruct (empty_choice_pair_parent _ _ _ _ _ HC HV HD) as [a [b ->]].
  destruct (empty_choice_domain_parent _ _ _ _ _ _ HC HD HE) as [A [HA HJ]].
  destruct (IH a b A eq_refl HA) as [HVa | [a' Hstep]].
  - exfalso. exact (erased_empty_check_value_luna [] a A HA eq_refl HVa HJ).
  - exists (TPair a' b). apply st_pair1, Hstep.
Qed.
End SignatureLemmas.

(* Checked signature-transport component: ErasureCounterexample. *)
Module ErasureCounterexample.
(* A counterexample to sort-endpoint reflection through phi_erase.
   It does not refute progress or Pi-codomain injectivity. *)

Import ListNotations TypeRulesCore.
Import _tmp_epstep _work_mixed_closure
  _work_cjoin _work_cstep_invariants.

(* GLM worker 1 — step_lift_glm: lifting commutes with small-step reduction. *)


Import ListNotations.


Theorem step_lift_glm : forall t u, step t u -> forall d k,
    step (lift d k t) (lift d k u).
Proof.
  intros t u H.
  induction H; intros d kk;
    try solve [cbn; constructor; eauto];
    try solve [cbn;
               repeat rewrite (lift_lift_one_zero _ d kk);
               repeat rewrite (lift_lift_one_one _ d kk);
               repeat rewrite (lift_lift_one_zero _ d kk);
               repeat rewrite (lift_lift_two_zero _ d kk);
               constructor];
    try solve [cbn; rewrite lift_subst_zero_comm; constructor].
  - (* st_case: raw case reduction — the side conditions transport through
       nth_error_lift_branches and enum_pos_lift_id. *)
    cbn. rewrite lift_subst_zero_comm.
    eapply st_case with (k := k) (c := lift d kk c) (b := lift d (S kk) b)
                        (n := n).
    + eapply nth_error_lift_branches; exact H.
    + rewrite (enum_pos_lift_id c n H0 d kk). exact H0.
    + rewrite (enum_pos_lift_id a n H1 d kk). exact H1.
    + intros j cj bj Hj Hnthj.
      rewrite nth_error_map in Hnthj.
      destruct (nth_error bs j) as [[cj0 bj0]|] eqn:Horig;
        cbn in Hnthj; [|discriminate].
      inversion Hnthj; subst.
      destruct (H2 j cj0 bj0 Hj Horig) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite (enum_pos_lift_id cj0 nj Hpos d kk). exact Hpos.
      * exact Hneq.
  - (* st_case_lbl: clause labels evaluate in place — congruence under map. *)
    cbn. rewrite !map_app. cbn [map].
    constructor; eauto.
Qed.


Import ListNotations TypeRulesCore.

Lemma fstep_lift_parent : forall t u, fstep t u -> forall d k,
  fstep (lift d k t) (lift d k u).
Proof.
  intros t u H. induction H; intros d k; cbn [lift];
    try solve [constructor; eauto using step_lift_glm].
  - rewrite lift_lift_one_zero. apply fs_eta.
  - repeat rewrite map_app. cbn. apply fs_case_br1. apply IHfstep.
  - repeat rewrite map_app. cbn. apply fs_case_br2. apply IHfstep.
Qed.

Lemma fconv_lift_parent : forall t u, fconv t u -> forall d k,
  fconv (lift d k t) (lift d k u).
Proof.
  intros t u H. induction H; intros d k.
  - apply fc_step, fstep_lift_parent, H.
  - apply fc_refl.
  - apply fc_sym, IHfconv.
  - eapply fc_trans; eauto.
Qed.


(* Direct, phase-order-independent erasure consumer.  The only premise is
   reflection of a combined path from an erased term to a stable sort. *)


Import ListNotations TypeRulesCore.
Fixpoint branch_erase (t : term) : term :=
  match t with
  | TVar n => TVar n | TSort k => TSort k
  | TPi A B => TPi (branch_erase A) (branch_erase B)
  | TLam b => TLam (branch_erase b)
  | TApp f a => TApp (branch_erase f) (branch_erase a)
  | TSigma A B => TSigma (branch_erase A) (branch_erase B)
  | TPair a b => TPair (branch_erase a) (branch_erase b)
  | TFst p => TFst (branch_erase p) | TSnd p => TSnd (branch_erase p)
  | TUnitT => TUnitT | TUnit => TUnit | TUId => TUId | TTag s => TTag s
  | TEnumU => TEnumU | TNilE => TNilE
  | TConsE t E => TConsE (branch_erase t) (branch_erase E)
  | TEnumT E => TEnumT (branch_erase E)
  | TEZero => TEZero | TESucc n => TESucc (branch_erase n)
  | TEPi E P => TEPi (branch_erase E) (branch_erase P)
  | TSwitch E P p e =>
      TSwitch (branch_erase E) (branch_erase P) (branch_erase p) (branch_erase e)
  | TIDesc IT => TIDesc (branch_erase IT) | TIVar i => TIVar (branch_erase i)
  | TI1 => TI1
  | TIProd A B => TIProd (branch_erase A) (branch_erase B)
  | TIPi Sd T => TIPi (branch_erase Sd) (branch_erase T)
  | TISig Sd T => TISig (branch_erase Sd) (branch_erase T)
  | TIChoice E T => TIChoice (branch_erase E) (branch_erase T)
  | TInterp D X => TInterp (branch_erase D) (branch_erase X)
  | TMuI R => TMuI (branch_erase R)
  | TMuS Sf => TMuS (TLam (TFst (TApp (lift 1 0 (branch_erase Sf)) (TVar 0))))
  | TIn x => TIn (branch_erase x)
  | TInd R P stp i x =>
      TInd (branch_erase R) (branch_erase P) (branch_erase stp)
           (branch_erase i) (branch_erase x)
  | TIAll D X xs P =>
      TIAll (branch_erase D) (branch_erase X) (branch_erase xs) (branch_erase P)
  | THyps D X P h xs =>
      THyps (branch_erase D) (branch_erase X) (branch_erase P)
            (branch_erase h) (branch_erase xs)
  | TList A => TList (branch_erase A)
  | TLNil A => TLNil (branch_erase A)
  | TLCons A a l => TLCons (branch_erase A) (branch_erase a) (branch_erase l)
  | TCase M Q bs =>
      TCase (branch_erase M) (branch_erase Q)
        (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs)
  end.
Lemma branch_erase_lift : forall t d k,
    branch_erase (lift d k t) = lift d k (branch_erase t).
Proof.
  assert (Hmap : forall bs d k,
      (forall c b, In (c,b) bs ->
       branch_erase (lift d k c) = lift d k (branch_erase c) /\
       branch_erase (lift d (S k) b) = lift d (S k) (branch_erase b)) ->
      map (fun '(c,b) => (branch_erase c, branch_erase b))
          (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs) =
      map (fun '(c,b) => (lift d k c, lift d (S k) b))
          (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs)).
  {
    intros bs d k H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity|].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall d k,
    branch_erase (lift d k t) = lift d k (branch_erase t))).
  intros t IH d k. destruct t; cbn.
  all: try solve [destruct k as [|k]; cbn; [reflexivity |];
                  destruct (Nat.leb n k); reflexivity].
  all: try solve [repeat f_equal; try reflexivity;
    try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia)].
  all: try (apply f_equal3).
  all: try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia).
  all: try solve [
    f_equal; f_equal; f_equal; f_equal;
    change (lift 1 0 (branch_erase (lift d k t)) =
      lift d (S k) (lift 1 0 (branch_erase t)));
    rewrite (IH t ltac:(cbn; lia) d k);
    replace (S k) with (1+k) by lia;
    symmetry; apply lift_lift_comm; lia ].
  all: apply Hmap; intros c b Hin; split;
    [ apply IH; eapply tsize_case_bs; exact Hin
    | apply IH; eapply tsize_case_bs_body; exact Hin ].
Qed.


Lemma branch_erase_subst : forall t u k,
    branch_erase (subst u k t) = subst (branch_erase u) k (branch_erase t).
Proof.
  assert (Hmap : forall bs u k,
      (forall c b, In (c,b) bs ->
       branch_erase (subst u k c) = subst (branch_erase u) k (branch_erase c) /\
       branch_erase (subst u (S k) b) =
         subst (branch_erase u) (S k) (branch_erase b)) ->
      map (fun '(c,b) => (branch_erase c, branch_erase b))
          (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs) =
      map (fun '(c,b) =>
             (subst (branch_erase u) k c,
              subst (branch_erase u) (S k) b))
          (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs)).
  {
    intros bs u k H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity|].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall u k,
    branch_erase (subst u k t) = subst (branch_erase u) k (branch_erase t))).
  intros t IH u k. destruct t; cbn.
  all: try solve [destruct k as [|k]; cbn;
    [ destruct n; cbn; try reflexivity;
      rewrite branch_erase_lift; reflexivity
    | destruct (Nat.leb n k); cbn; try reflexivity;
      destruct (Nat.eqb n (S k)); cbn; try reflexivity;
      rewrite branch_erase_lift; reflexivity ]].
  all: try (f_equal; try reflexivity;
    try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia)).
  all: try (apply f_equal3).
  all: try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia).
  all: try solve [
    f_equal; f_equal; f_equal; f_equal;
    rewrite (IH t ltac:(cbn; lia) u k);
    rewrite subst_lift_one_zero; reflexivity ].
  all: apply Hmap; intros c b Hin; split;
    [ apply IH; eapply tsize_case_bs; exact Hin
    | apply IH; eapply tsize_case_bs_body; exact Hin ].
Qed.


Import ListNotations TypeRulesCore.

Lemma branch_erase_enum_pos : forall c n, enum_pos c n ->
    enum_pos (branch_erase c) n.
Proof. intros c n H. induction H; cbn; constructor; assumption. Qed.

Lemma branch_erase_nth_error : forall bs k c b,
    nth_error bs k = Some (c,b) ->
    nth_error (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs) k =
      Some (branch_erase c, branch_erase b).
Proof.
  intros bs k. revert k.
  induction bs as [|[c0 b0] bs IH]; intros [|k] c b H;
    cbn in *; try discriminate.
  - inversion H; reflexivity.
  - apply IH; exact H.
Qed.

Lemma branch_erase_nth_inv : forall bs k c b,
    nth_error (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs) k =
      Some (c,b) ->
    exists c0 b0, nth_error bs k = Some (c0,b0) /\
      branch_erase c0 = c /\ branch_erase b0 = b.
Proof.
  intros bs k. revert k.
  induction bs as [|[c0 b0] bs IH];
    intros [|k] c b H; cbn in *; try discriminate.
  - inversion H; subst. eexists; eexists; repeat split; reflexivity.
  - destruct (IH k c b H) as [c1 [b1 [H1 [H2 H3]]]].
    exists c1, b1. repeat split; cbn; assumption.
Qed.

Lemma branch_erase_step : forall t u,
    step t u -> step (branch_erase t) (branch_erase u).
Proof.
  intros t u H; induction H.
  all: cbn; try constructor; eauto.
  - rewrite branch_erase_subst. apply st_beta.
  - repeat rewrite branch_erase_lift. apply st_epi_cons.
  - repeat rewrite branch_erase_lift. apply st_switch_succ.
  - repeat rewrite branch_erase_lift. apply st_interp_prod.
  - repeat rewrite branch_erase_lift. apply st_interp_pi.
  - repeat rewrite branch_erase_lift. apply st_interp_sig.
  - repeat rewrite branch_erase_lift. apply st_interp_choice.
  - repeat rewrite branch_erase_lift. apply st_iall_prod.
  - repeat rewrite branch_erase_lift. apply st_iall_pi.
  - repeat rewrite branch_erase_lift. apply st_hyps_pi.
  - repeat rewrite branch_erase_lift. apply st_ind.
  - rewrite branch_erase_subst.
    apply st_case with
      (a := branch_erase a) (xs := branch_erase xs) (Q := branch_erase Q)
      (bs := map (fun '(c,b) => (branch_erase c, branch_erase b)) bs)
      (k := k) (c := branch_erase c) (b := branch_erase b) (n := n).
    + apply branch_erase_nth_error. exact H.
    + apply branch_erase_enum_pos. exact H0.
    + apply branch_erase_enum_pos. exact H1.
    + intros j cj bj Hj Hnth.
      destruct (branch_erase_nth_inv _ _ _ _ Hnth)
        as [cj0 [bj0 [Hsrc [Hc Hb]]]].
      destruct (H2 j cj0 bj0 Hj Hsrc) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite <- Hc. apply branch_erase_enum_pos. exact Hpos.
      * exact Hneq.
  - repeat rewrite map_app. cbn.
    apply st_case_lbl. exact IHstep.
Qed.

Lemma branch_erase_conv : forall t u, conv t u ->
    fconv (branch_erase t) (branch_erase u).
Proof.
  intros t u H. induction H; cbn; eauto using fconv, fstep, branch_erase_step.
  all: try (eapply fconv_map; eauto using fstep).
  all: try (eapply fconv_map2; eauto using fstep).
  all: try (eapply fconv_map3; eauto using fstep).
  all: try (eapply fconv_map4; eauto using fstep).
  all: try (eapply fconv_map5; eauto using fstep).
  all: try (rewrite branch_erase_lift; apply fc_step, fs_eta).
  all: try (repeat rewrite map_app; cbn;
    eapply fconv_map2; eauto using fstep).
  - apply (fconv_map TLam); [intros; apply fs_lam; assumption |].
    apply (fconv_map TFst); [intros; apply fs_fst; assumption |].
    apply (fconv_map (fun z => TApp z (TVar 0)));
      [intros; apply fs_app1; assumption |].
    apply fconv_lift_parent. exact IHconv.
  - eapply (fconv_map2
      (fun x y => TCase x y
        (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs)));
      eauto using fstep.
  - repeat rewrite map_app. cbn.
    eapply (fconv_map2
      (fun x y => TCase (branch_erase M) (branch_erase Q)
        (map (fun '(c,b) => (branch_erase c, branch_erase b)) bs1 ++
         (x,y) :: map (fun '(c,b) => (branch_erase c, branch_erase b)) bs2)));
      eauto using fstep.
Qed.


Import ListNotations TypeRulesCore.

Definition bad_t : term :=
  TSnd (TLam (TApp (TPair (TMuS (TVar 0)) (TSort 0)) (TVar 0))).
Definition bad_u : term :=
  TSnd (TPair (TMuS TUnit) (TSort 0)).

Lemma bad_phi : phi_erase bad_t =
    TSnd (TLam (TApp (TPair (TMuS TUnit) (TSort 0)) (TVar 0))).
Proof. reflexivity. Qed.

Lemma bad_ep : epstep (phi_erase bad_t) bad_u.
Proof.
  unfold bad_t, bad_u.
  cbn [phi_erase].
  apply eps_snd.
  change (epstep (TLam (TApp (lift 1 0 (TPair (TMuS TUnit) (TSort 0))) (TVar 0)))
    (TPair (TMuS TUnit) (TSort 0))).
  apply eps_eta. apply epstep_refl.
Qed.

Lemma bad_u_sort : pstep bad_u (TSort 0).
Proof.
  unfold bad_u.
  eapply ps_snd_pair; apply pstep_refl.
Qed.


Lemma bad_pstep_id : forall u, pstep bad_t u -> u = bad_t.
Proof.
  intros u H. unfold bad_t in *.
  inversion H; subst; clear H.
  repeat match goal with
  | Hx : pstep (TLam _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TApp (TPair _ _) (TVar 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TPair (TMuS (TVar 0)) (TSort 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TMuS (TVar 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TVar 0) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TSort 0) _ |- _ => inversion Hx; subst; clear Hx
  end.
  reflexivity.
Qed.


Ltac glm_shape :=
  match goal with
  | H : lift 1 _ ?f = _ |- _ =>
      destruct f; cbn [lift] in H;
      repeat match goal with
             | H0 : context [Nat.ltb ?n ?k] |- _ => destruct (Nat.ltb n k)
             end;
      cbn [lift] in H; try discriminate
  end.


Lemma lift_shape_fst_glm : forall k f p,
    lift 1 k f = TFst p -> exists p0, f = TFst p0 /\ p = lift 1 k p0.
Proof.
  intros k f p H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.
Lemma lift_shape_mus_glm : forall k f Sf,
    lift 1 k f = TMuS Sf -> exists Sf0, f = TMuS Sf0 /\ Sf = lift 1 k Sf0.
Proof.
  intros k f Sf H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.
Lemma lift_shape_lam_glm : forall k f b,
    lift 1 k f = TLam b -> exists b0, f = TLam b0 /\ b = lift 1 (S k) b0.
Proof.
  intros k f b H. glm_shape. eexists. split; [reflexivity | congruence].
Qed.
Lemma lift_shape_app_glm : forall k f g a,
    lift 1 k f = TApp g a ->
    exists g0 a0, f = TApp g0 a0 /\ g = lift 1 k g0 /\ a = lift 1 k a0.
Proof.
  intros k f g a H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.
Lemma lift_shape_pair_glm : forall k f a b,
    lift 1 k f = TPair a b ->
    exists a0 b0, f = TPair a0 b0 /\ a = lift 1 k a0 /\ b = lift 1 k b0.
Proof.
  intros k f a b H. glm_shape. eexists; eexists.
  split; [reflexivity | split; congruence].
Qed.


Import ListNotations TypeRulesCore.

Definition branch_bad : term := branch_erase bad_t.

Lemma branch_bad_def : branch_bad =
  TSnd (TLam (TApp
    (TPair (TMuS (TLam (TFst (TApp (TVar 1) (TVar 0))))) (TSort 0))
    (TVar 0))).
Proof. reflexivity. Qed.

Lemma branch_bad_pstep_id : forall u, pstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. rewrite branch_bad_def in *.
  inversion H; subst; clear H.
  repeat match goal with
  | Hx : pstep (TLam _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TApp (TPair _ _) (TVar 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TPair (TMuS _) (TSort 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TMuS _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TLam (TFst _)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TFst _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TApp (TVar _) (TVar _)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TVar _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : pstep (TSort 0) _ |- _ => inversion Hx; subst; clear Hx
  end.
  reflexivity.
Qed.

Lemma lift_var_neq : forall k g, lift 1 k g <> TVar k.
Proof.
  intros k g H. destruct g; try discriminate H.
  change ((if Nat.ltb n k then TVar n else TVar (S n)) = TVar k) in H.
  destruct (Nat.ltb n k) eqn:E.
  - apply Nat.ltb_lt in E. injection H as Hn. lia.
  - apply Nat.ltb_ge in E. injection H as Hn. lia.
Qed.

Lemma lift_pair_neq : forall f,
    lift 1 0 f <> TPair (TMuS (TLam (TFst (TApp (TVar 1) (TVar 0))))) (TSort 0).
Proof.
  intros f H.
  destruct (lift_shape_pair_glm _ _ _ _ H) as [a [b [_ [Ha _]]]].
  destruct (lift_shape_mus_glm _ _ _ (eq_sym Ha)) as [s [_ Hs]].
  destruct (lift_shape_lam_glm _ _ _ (eq_sym Hs)) as [body [_ Hb]].
  destruct (lift_shape_fst_glm _ _ _ (eq_sym Hb)) as [app [_ Happ]].
  destruct (lift_shape_app_glm _ _ _ _ (eq_sym Happ)) as [v [w [_ [Hv _]]]].
  exact (lift_var_neq 1 v (eq_sym Hv)).
Qed.

Lemma branch_bad_epstep_id : forall u, epstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. rewrite branch_bad_def in *.
  inversion H; subst; clear H.
  repeat match goal with
  | Hx : epstep (TLam _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TApp (TPair _ _) (TVar 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TPair (TMuS _) (TSort 0)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TMuS _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TLam (TFst _)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TFst _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TApp (TVar _) (TVar _)) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TVar _) _ |- _ => inversion Hx; subst; clear Hx
  | Hx : epstep (TSort 0) _ |- _ => inversion Hx; subst; clear Hx
  end.
  all: try reflexivity.
  all: exfalso; match goal with
  | H : TPair _ _ = lift 1 0 ?f |- _ => exact (lift_pair_neq f (eq_sym H))
  | H : lift 1 0 ?f = TPair _ _ |- _ => exact (lift_pair_neq f H)
  end.
Qed.

Lemma branch_bad_rtc_pstep_id : forall u, rtc pstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. remember branch_bad as x eqn:Hx.
  induction H; subst; [reflexivity|].
  pose proof (branch_bad_pstep_id _ H) as ->. apply IHrtc. reflexivity.
Qed.

Lemma branch_bad_rtc_epstep_id : forall u, rtc epstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. remember branch_bad as x eqn:Hx.
  induction H; subst; [reflexivity|].
  pose proof (branch_bad_epstep_id _ H) as ->. apply IHrtc. reflexivity.
Qed.

Lemma branch_bad_cstep_id : forall u, cstep branch_bad u -> u = branch_bad.
Proof. intros u H; inversion H; subst; [eapply branch_bad_rtc_pstep_id|eapply branch_bad_rtc_epstep_id]; eassumption. Qed.

Lemma branch_bad_rtc_cstep_id : forall u, rtc cstep branch_bad u -> u = branch_bad.
Proof.
  intros u H. remember branch_bad as x eqn:Hx.
  induction H; subst; [reflexivity|].
  pose proof (branch_bad_cstep_id _ H) as ->. apply IHrtc. reflexivity.
Qed.


Import ListNotations TypeRulesCore.

Lemma bad_not_conv_sort : forall j, ~ conv bad_t (TSort j).
Proof.
  intros j Hc.
  pose proof (branch_erase_conv bad_t (TSort j) Hc) as Hfc.
  destruct (fconv_cjoin _ _ Hfc) as [w [Hw1 Hw2]].
  pose proof (branch_bad_rtc_cstep_id w Hw1) as Hw.
  subst w.
  cbn [branch_erase] in Hw2.
  pose proof (rtc_cstep_sort_id _ _ Hw2) as Heq.
  rewrite branch_bad_def in Heq.
  discriminate Heq.
Qed.

Lemma bad_erased_sort_path : rtc cstep (phi_erase bad_t) (TSort 0).
Proof.
  eapply rtc_step.
  - apply epstep_cstep. exact bad_ep.
  - eapply rtc_step.
    + apply pstep_cstep. exact bad_u_sort.
    + apply rtc_refl.
Qed.

Theorem phi_erase_sort_endpoint_not_reflectable :
  ~ (forall t j, rtc cstep (phi_erase t) (TSort j) -> conv t (TSort j)).
Proof.
  intro H. exact (bad_not_conv_sort 0 (H bad_t 0 bad_erased_sort_path)).
Qed.
End ErasureCounterexample.

(* Checked signature-transport component: SignatureConversion. *)
Module SignatureConversion.
(* Checked support for signature conversion and the progress induction.
   The bounded-progress premise below is the induction hypothesis on smaller
   terms. It is an explicit premise, not an assumed global progress theorem.
   The final theorem handles a direct Eq-phi step; it does not assert the
   still-open transport theorem for arbitrary beta/eta/phi conversion. *)
Import SignatureLemmas ErasureCounterexample.
Import ListNotations TypeRulesCore _tmp_epstep
 _tmp_epstep_subst _tmp_commute
 _work_mixed_closure _work_cjoin
 _work_cstep_invariants _work_conv_whd_pos
 _luna_phi_erase_shapes MuApplicationSort.

(* _luna_finish_erased_sigma_value *)
Lemma sigma_cjoin_hshape_tag_luna : forall t u h1 h2,
    cjoin t u -> hshape t h1 -> hshape u h2 -> h1 = h2.
Proof.
  intros t u h1 h2 [w [Ht Hu]] Htshape Hushape.
  pose proof (rtc_cstep_hshape _ _ Ht h1 Htshape) as Hw1.
  pose proof (rtc_cstep_hshape _ _ Hu h2 Hushape) as Hw2.
  eapply hshape_tag_unique; eassumption.
Qed.

Lemma sigma_phi_erase_sort_luna : forall k, hshape (phi_erase (TSort k)) HSort.
Proof. intros; cbn; constructor. Qed.

Lemma sigma_phi_erase_pi_luna : forall A B,
    hshape (phi_erase (TPi A B)) HPi.
Proof. intros; cbn; constructor. Qed.

Lemma sigma_phi_erase_carrier_luna : forall E Sf i,
    hshape (phi_erase (TApp (Carrier E Sf) i)) HMuIApp.
Proof. intros; cbn [phi_erase Carrier]; constructor. Qed.

Lemma sigma_phi_erase_musapp_luna : forall Sf i,
    hshape (phi_erase (TApp (TMuS Sf) i)) HMuSApp.
Proof. intros; cbn [phi_erase]; constructor. Qed.

Lemma erased_sigma_sub_back : forall G X Y,
    sub G X Y -> forall A B,
    cjoin (phi_erase Y) (TSigma A B) ->
    cjoin (phi_erase X) (TSigma A B).
Proof.
  intros G X Y Hsub. induction Hsub; intros A0 B0 Hjoin.
  - eapply cjoin_trans; [apply conv_phi_cjoin; exact H | exact Hjoin].
  - exact (IHHsub1 A0 B0 (IHHsub2 A0 B0 Hjoin)).
  - exfalso. assert (Heq : HSort = HSigma).
    { eapply (sigma_cjoin_hshape_tag_luna _ _ _ _ Hjoin).
      - apply sigma_phi_erase_sort_luna.
      - constructor. }
    discriminate Heq.
  - exfalso. assert (Heq : HPi = HSigma).
    { eapply (sigma_cjoin_hshape_tag_luna _ _ _ _ Hjoin).
      - apply sigma_phi_erase_pi_luna.
      - constructor. }
    discriminate Heq.
  - exfalso. assert (Heq : HMuIApp = HSigma).
    { eapply (sigma_cjoin_hshape_tag_luna _ _ _ _ Hjoin).
      - apply sigma_phi_erase_carrier_luna.
      - constructor. }
    discriminate Heq.
  - exfalso. assert (Heq : HMuSApp = HSigma).
    { eapply (sigma_cjoin_hshape_tag_luna _ _ _ _ Hjoin).
      - apply sigma_phi_erase_musapp_luna.
      - constructor. }
    discriminate Heq.
Qed.

Lemma clash_sigma_luna : forall T A B h,
    cjoin (phi_erase T) (TSigma A B) ->
    hshape (phi_erase T) h -> h <> HSigma -> False.
Proof.
  intros T A B h HJ HH Hneq.
  pose proof (sigma_cjoin_hshape_tag_luna _ _ _ _ HJ HH
    (hs_sigma A B)) as E.
  exact (Hneq E).
Qed.

Lemma erased_sigma_synth_value_absurd : forall t T,
    synth [] t T -> value t -> forall A B,
    cjoin (phi_erase T) (TSigma A B) -> False.
Proof.
  intros t T Hsyn HV A B HJ.
  inversion Hsyn; subst; try solve [inversion HV].
  all: try solve [
    eapply clash_sigma_luna; [exact HJ | cbn [phi_erase]; constructor | discriminate] ].
  pose proof (value_app_synth_sort _ _ _ HV Hsyn) as Hsort.
  rewrite Hsort in HJ.
  eapply clash_sigma_luna; [exact HJ | apply sigma_phi_erase_sort_luna | discriminate].
Qed.

Lemma erased_sigma_check_value_pair : forall G t T,
    check G t T -> G = [] -> value t -> forall A B,
    cjoin (phi_erase T) (TSigma A B) -> exists a b, t = TPair a b.
Proof.
  intros G t T Hcheck.
  induction Hcheck; intros HG HV A0 B0 HJ; subst.
  all: try solve [inversion HV].
  all: try solve [exfalso; eapply clash_sigma_luna;
    [exact HJ | cbn [phi_erase]; constructor | discriminate]].
  - exfalso. eapply erased_sigma_synth_value_absurd; [exact H | exact HV |].
    eapply cjoin_trans; [apply conv_phi_cjoin; exact H0 | exact HJ].
  - apply (IHHcheck eq_refl HV A0 B0).
    eapply erased_sigma_sub_back; [exact H | exact HJ].
  - apply (IHHcheck eq_refl HV A0 B0).
    eapply cjoin_trans; [apply conv_phi_cjoin, cv_sym; exact H | exact HJ].
  - eexists; eexists; reflexivity.
  - assert (HCapp : check [] (TApp f a) (subst a 0 B)).
    { eapply ch_app; eassumption. }
    destruct (SignatureLemmas.luna_check_app_erased_sort
      f a (subst a 0 B) HCapp HV) as [j Hj].
    assert (HJ' : cjoin (TSort j) (TSigma A0 B0)).
    { eapply cjoin_trans; [apply cjoin_sym; exact Hj | exact HJ]. }
    exfalso. eapply (clash_sigma_luna (TSort j) A0 B0 HSort);
      [exact HJ' | apply hs_sort | discriminate].
Qed.

(* _luna_finish_erased_enum_value *)
Lemma enum_cjoin_tag_luna : forall t u h k,
    cjoin t u -> hshape t h -> hshape u k -> h = k.
Proof.
  intros t u h k [w [Ht Hu]] HH HK.
  pose proof (rtc_cstep_hshape _ _ Ht h HH) as H1.
  pose proof (rtc_cstep_hshape _ _ Hu k HK) as H2.
  eapply hshape_tag_unique; eassumption.
Qed.

Lemma enum_cjoin_inv_luna : forall E1 E2,
    cjoin (TEnumT E1) (TEnumT E2) -> cjoin E1 E2.
Proof.
  intros E1 E2 [w [H1 H2]].
  destruct (rtc_cstep_enumt_inv _ _ H1) as [W1 [HW1 HE1]].
  destruct (rtc_cstep_enumt_inv _ _ H2) as [W2 [HW2 HE2]].
  rewrite HW1 in HW2. inversion HW2; subst W2.
  exists W1. split; assumption.
Qed.

Lemma enum_cjoin_sub_back_luna : forall G X Y,
    sub G X Y -> forall E,
    cjoin (phi_erase Y) (TEnumT E) ->
    cjoin (phi_erase X) (TEnumT E).
Proof.
  intros G X Y Hsub. induction Hsub; intros E0 HJ.
  - eapply cjoin_trans; [apply conv_phi_cjoin; exact H | exact HJ].
  - exact (IHHsub1 E0 (IHHsub2 E0 HJ)).
  - exfalso. pose proof (enum_cjoin_tag_luna _ _ _ _ HJ
      (hs_sort _) (hs_enumt _)) as K; discriminate K.
  - exfalso. pose proof (enum_cjoin_tag_luna _ _ _ _ HJ
      (hs_pi _ _) (hs_enumt _)) as K; discriminate K.
  - exfalso. pose proof (enum_cjoin_tag_luna _ _ _ _ HJ
      (hs_muiapp _ _) (hs_enumt _)) as K; discriminate K.
  - exfalso. pose proof (enum_cjoin_tag_luna _ _ _ _ HJ
      (hs_musapp _ _) (hs_enumt _)) as K; discriminate K.
Qed.

Lemma clash_enum_luna : forall T E h,
    cjoin (phi_erase T) (TEnumT E) ->
    hshape (phi_erase T) h -> h <> HEnumT -> False.
Proof.
  intros T E h HJ HH Hneq.
  pose proof (enum_cjoin_tag_luna _ _ _ _ HJ HH (hs_enumt E)) as K.
  exact (Hneq K).
Qed.

Lemma enum_cjoin_synth_value_absurd_luna : forall t T,
    synth [] t T -> value t -> forall E,
    cjoin (phi_erase T) (TEnumT E) -> False.
Proof.
  intros t T Hsyn HV E HJ.
  inversion Hsyn; subst; try solve [inversion HV].
  all: try solve [eapply clash_enum_luna;
    [exact HJ | cbn [phi_erase]; constructor | discriminate]].
  pose proof (value_app_synth_sort _ _ _ HV Hsyn) as Hsort.
  rewrite Hsort in HJ.
  eapply clash_enum_luna; [exact HJ | apply hs_sort | discriminate].
Qed.

Lemma erased_enum_check_value_origin_luna : forall G t T,
    check G t T -> G = [] -> value t -> forall E,
    cjoin (phi_erase T) (TEnumT E) ->
    (exists tg E0, t = TEZero /\
       cjoin (TConsE (phi_erase tg) (phi_erase E0)) E) \/
    (exists n tg E0, t = TESucc n /\ check [] n (TEnumT E0) /\
       cjoin (TConsE (phi_erase tg) (phi_erase E0)) E).
Proof.
  intros G t T Hcheck.
  induction Hcheck; intros HG HV E0 HJ; subst.
  all: try solve [inversion HV].
  all: try solve [exfalso; eapply clash_enum_luna;
    [exact HJ | cbn [phi_erase]; constructor | discriminate]].
  - exfalso. eapply enum_cjoin_synth_value_absurd_luna;
      [exact H | exact HV |].
    eapply cjoin_trans; [apply conv_phi_cjoin; exact H0 | exact HJ].
  - apply (IHHcheck eq_refl HV E0).
    eapply enum_cjoin_sub_back_luna; [exact H | exact HJ].
  - apply (IHHcheck eq_refl HV E0).
    eapply cjoin_trans; [apply conv_phi_cjoin, cv_sym; exact H | exact HJ].
  - assert (HCapp : check [] (TApp f a) (subst a 0 B)).
    { eapply ch_app; eassumption. }
    destruct (SignatureLemmas.luna_check_app_erased_sort
      f a (subst a 0 B) HCapp HV) as [j Hj].
    assert (HJ' : cjoin (TSort j) (TEnumT E0)).
    { eapply cjoin_trans; [apply cjoin_sym; exact Hj | exact HJ]. }
    exfalso. eapply (clash_enum_luna (TSort j) E0 HSort);
      [exact HJ' | apply hs_sort | discriminate].
  - left. eexists; eexists; split; [reflexivity |].
    cbn [phi_erase] in HJ. eapply enum_cjoin_inv_luna; exact HJ.
  - right. exists n, tg, E. repeat split; try reflexivity; try exact Hcheck2.
    cbn [phi_erase] in HJ. eapply enum_cjoin_inv_luna; exact HJ.
Qed.

(* _luna_finish_interp_pair_origin *)
Lemma eval_interp_luna : forall D D' X,
    eval D D' -> eval (TInterp D X) (TInterp D' X).
Proof.
  intros D D' X H. induction H.
  - apply ev_refl.
  - eapply ev_step; [apply st_interp1; exact H | exact IHeval].
Qed.

Lemma eval_trans_luna : forall t u v,
    eval t u -> eval u v -> eval t v.
Proof.
  intros t u v H. induction H; intros Huv.
  - exact Huv.
  - eapply ev_step; [exact H | apply IHeval; exact Huv].
Qed.

Lemma erased_pair_interp_prod_origin : forall a b T D X A B,
    check [] (TPair a b) T ->
    cjoin (phi_erase T) (phi_erase (TInterp D X)) ->
    eval D (TIProd A B) ->
    exists TA TB,
      check [] a TA /\ check [] b TB /\
      cjoin (phi_erase TA) (phi_erase (TInterp A X)) /\
      cjoin (phi_erase TB) (phi_erase (TInterp B X)).
Proof.
  intros a b T D X A B Hcheck Hjoin Heval.
  destruct (pair_origin [] a b T Hcheck)
    as [TA [B0 [Ha [Hb Horigin]]]].
  pose proof (eval_interp_luna D (TIProd A B) X Heval) as HevalI.
  assert (HevalStep : eval (TInterp (TIProd A B) X)
      (TSigma (TInterp A X) (lift 1 0 (TInterp B X)))).
  { eapply ev_step; [eapply st_interp_prod; eauto using pstep_refl | apply ev_refl]. }
  pose proof (eval_trans_luna _ _ _ HevalI HevalStep) as Heval'.
  pose proof (phi_erase_eval_csteps _ _ Heval') as Hred.
  destruct (cjoin_reduce_right _ _ _ Hjoin Hred) as [w [Hw1 Hw2]].
  pose proof (erased_sigma_sub_back [] (TSigma TA B0) T Horigin _ _
    (ex_intro _ w (conj Hw1 Hw2))) as Hsig.
  destruct (cjoin_sigma_inv_luna _ _ _ _ Hsig)
    as [HAjoin HBjoin].
  assert (Hsub : cjoin
        (subst (phi_erase a) 0 (phi_erase B0))
        (subst (phi_erase a) 0
          (phi_erase (lift 1 0 (TInterp B X))))).
  { unfold cjoin in HBjoin. destruct HBjoin as [q [HL HR]].
    exists (subst (phi_erase a) 0 q). split;
      [eapply rtc_cstep_subst_luna; exact HL
      |eapply rtc_cstep_subst_luna; exact HR]. }
  cbn [phi_erase] in Hsub.
  rewrite phi_erase_lift in Hsub.
  rewrite subst_lift_zero in Hsub.
  assert (Hsub' : cjoin (phi_erase (subst a 0 B0))
      (phi_erase (TInterp B X))).
  { rewrite phi_erase_subst. exact Hsub. }
  exists TA, (subst a 0 B0). repeat split; assumption.
Qed.

Lemma erased_pair_interp_choice_origin : forall a b T D X E F,
    check [] (TPair a b) T ->
    cjoin (phi_erase T) (phi_erase (TInterp D X)) ->
    eval D (TIChoice E F) ->
    exists TA TB,
      check [] a TA /\ check [] b TB /\
      cjoin (phi_erase TA) (phi_erase (TEnumT E)) /\
      cjoin (phi_erase TB) (phi_erase (TInterp (TApp F a) X)).
Proof.
  intros a b T D X E F Hcheck Hjoin Heval.
  destruct (pair_origin [] a b T Hcheck)
    as [TA [B0 [Ha [Hb Horigin]]]].
  pose proof (eval_interp_luna D (TIChoice E F) X Heval) as HevalI.
  assert (HevalStep : eval (TInterp (TIChoice E F) X)
      (TSigma (TEnumT E)
        (TInterp (TApp (lift 1 0 F) (TVar 0)) (lift 1 0 X)))).
  { eapply ev_step; [eapply st_interp_choice | apply ev_refl]. }
  pose proof (eval_trans_luna _ _ _ HevalI HevalStep) as Heval'.
  pose proof (phi_erase_eval_csteps _ _ Heval') as Hred.
  destruct (cjoin_reduce_right _ _ _ Hjoin Hred) as [w [Hw1 Hw2]].
  pose proof (erased_sigma_sub_back [] (TSigma TA B0) T Horigin _ _
    (ex_intro _ w (conj Hw1 Hw2))) as Hsig.
  destruct (cjoin_sigma_inv_luna _ _ _ _ Hsig)
    as [HAjoin HBjoin].
  assert (Hsub : cjoin
      (subst (phi_erase a) 0 (phi_erase B0))
      (subst (phi_erase a) 0
        (phi_erase (TInterp (TApp (lift 1 0 F) (TVar 0))
          (lift 1 0 X))))).
  { unfold cjoin in HBjoin. destruct HBjoin as [q [HL HR]].
    exists (subst (phi_erase a) 0 q). split;
      [eapply rtc_cstep_subst_luna; exact HL
      |eapply rtc_cstep_subst_luna; exact HR]. }
  cbn [phi_erase subst] in Hsub.
  rewrite phi_erase_lift in Hsub.
  rewrite subst_lift_zero in Hsub.
  cbn in Hsub.
  rewrite _tmp_commute.lift_zero_id_local in Hsub.
  rewrite phi_erase_lift in Hsub.
  rewrite subst_lift_zero in Hsub.
  assert (Hsub' : cjoin (phi_erase (subst a 0 B0))
      (phi_erase (TInterp (TApp F a) X))).
  { rewrite phi_erase_subst. exact Hsub. }
  exists TA, (subst a 0 B0). repeat split; assumption.
Qed.

(* _parent_finish_cjoin_context *)
Lemma rtc_map_parent {A B : Type} (R : A -> A -> Prop) (S : B -> B -> Prop)
  (F : A -> B) (HF : forall t u,R t u -> S(F t)(F u)) :
  forall t u,rtc R t u -> rtc S(F t)(F u).
Proof. intros t u H; induction H; eauto using rtc_refl,rtc_step. Qed.

Lemma cstep_map_parent (F:term->term)
 (HP:forall t u,pstep t u->pstep(F t)(F u))
 (HE:forall t u,epstep t u->epstep(F t)(F u)) :
 forall t u,cstep t u->cstep(F t)(F u).
Proof.
 intros t u H; inversion H; subst.
 - apply cs_core. eapply rtc_map_parent; eassumption.
 - apply cs_eta. eapply rtc_map_parent; eassumption.
Qed.

Lemma cjoin_map_parent (F:term->term)
 (HP:forall t u,pstep t u->pstep(F t)(F u))
 (HE:forall t u,epstep t u->epstep(F t)(F u)) :
 forall t u,cjoin t u->cjoin(F t)(F u).
Proof.
 intros t u [w [HT HU]]. exists(F w). split;
 (eapply rtc_map_parent; [apply cstep_map_parent; eassumption | eassumption]).
Qed.

Lemma cjoin_map2_parent (F:term->term->term)
 (HP1:forall a b u,pstep a b->pstep(F a u)(F b u))
 (HP2:forall a b u,pstep a b->pstep(F u a)(F u b))
 (HE1:forall a b u,epstep a b->epstep(F a u)(F b u))
 (HE2:forall a b u,epstep a b->epstep(F u a)(F u b)) :
 forall a a' b b',cjoin a a'->cjoin b b'->cjoin(F a b)(F a' b').
Proof.
 intros a a' b b' HA HB. eapply cjoin_trans.
 - eapply (cjoin_map_parent (fun z=>F z b)); eauto.
 - eapply (cjoin_map_parent (fun z=>F a' z)); eauto.
Qed.

Lemma cjoin_sigma_parent : forall A A' B B',cjoin A A' -> cjoin B B' ->
 cjoin(TSigma A B)(TSigma A' B').
Proof.
 eapply cjoin_map2_parent; intros; constructor;
 eauto using pstep_refl,epstep_refl.
Qed.
Lemma cjoin_app_parent : forall A A' B B',cjoin A A' -> cjoin B B' ->
 cjoin(TApp A B)(TApp A' B').
Proof.
 eapply cjoin_map2_parent; intros; apply ps_app || apply eps_app;
 eauto using pstep_refl,epstep_refl.
Qed.
Lemma cjoin_interp_parent : forall A A' B B',cjoin A A' -> cjoin B B' ->
 cjoin(TInterp A B)(TInterp A' B').
Proof.
 eapply cjoin_map2_parent; intros; apply ps_interp || apply eps_interp;
 eauto using pstep_refl,epstep_refl.
Qed.
Lemma cjoin_enumt_parent : forall E E',cjoin E E'->cjoin(TEnumT E)(TEnumT E').
Proof. eapply cjoin_map_parent; intros; constructor; assumption. Qed.
Lemma cjoin_lift_parent : forall t u,cjoin t u->forall d k,cjoin(lift d k t)(lift d k u).
Proof.
 intros t u H d k. eapply cjoin_map_parent; [| |exact H]; intros.
 - apply pstep_lift; assumption.
 - apply epstep_lift; assumption.
Qed.

Lemma pstep_conse_inv_parent : forall A B u, pstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_conse_inv_parent : forall A B u, rtc pstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TConsE A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_conse_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_conse_inv_parent : forall A B u, epstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_conse_inv_parent : forall A B u, rtc epstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TConsE A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_conse_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_conse_inv_parent : forall A B u, cstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_conse_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_conse_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_conse_inv_parent : forall A B u, rtc cstep (TConsE A B) u ->
    exists A' B', u = TConsE A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TConsE A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_conse_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_conse_inv_parent : forall A1 B1 A2 B2,
    cjoin (TConsE A1 B1) (TConsE A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_conse_inv_parent _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_conse_inv_parent _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.


Lemma pstep_iprod_inv_parent : forall A B u, pstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_iprod_inv_parent : forall A B u, rtc pstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TIProd A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_iprod_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_iprod_inv_parent : forall A B u, epstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_iprod_inv_parent : forall A B u, rtc epstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TIProd A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_iprod_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_iprod_inv_parent : forall A B u, cstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_iprod_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_iprod_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_iprod_inv_parent : forall A B u, rtc cstep (TIProd A B) u ->
    exists A' B', u = TIProd A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TIProd A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_iprod_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_iprod_inv_parent : forall A1 B1 A2 B2,
    cjoin (TIProd A1 B1) (TIProd A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_iprod_inv_parent _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_iprod_inv_parent _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.


Lemma pstep_ichoice_inv_parent : forall A B u, pstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\ pstep A A' /\ pstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_pstep_ichoice_inv_parent : forall A B u, rtc pstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\
      rtc pstep A A' /\ rtc pstep B B'.
Proof.
  intros A B u H. remember (TIChoice A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (pstep_ichoice_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma epstep_ichoice_inv_parent : forall A B u, epstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\ epstep A A' /\ epstep B B'.
Proof. intros A B u H. inversion H; subst; eauto. Qed.

Lemma rtc_epstep_ichoice_inv_parent : forall A B u, rtc epstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\
      rtc epstep A A' /\ rtc epstep B B'.
Proof.
  intros A B u H. remember (TIChoice A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (epstep_ichoice_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cstep_ichoice_inv_parent : forall A B u, cstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\ cstep A A' /\ cstep B B'.
Proof.
  intros A B u H. inversion H; subst.
  - destruct (rtc_pstep_ichoice_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_core; assumption.
  - destruct (rtc_epstep_ichoice_inv_parent _ _ _ H0)
      as [A' [B' [-> [HA' HB']]]].
    exists A', B'. repeat split; apply cs_eta; assumption.
Qed.

Lemma rtc_cstep_ichoice_inv_parent : forall A B u, rtc cstep (TIChoice A B) u ->
    exists A' B', u = TIChoice A' B' /\
      rtc cstep A A' /\ rtc cstep B B'.
Proof.
  intros A B u H. remember (TIChoice A B) as t eqn:Ht. revert A B Ht.
  induction H; intros A B HE; subst.
  - exists A, B. repeat split; apply rtc_refl.
  - destruct (cstep_ichoice_inv_parent A B y H)
      as [A1 [B1 [-> [HA1 HB1]]]].
    destruct (IHrtc A1 B1 eq_refl)
      as [A2 [B2 [-> [HA2 HB2]]]].
    exists A2, B2. repeat split; eauto using rtc_step.
Qed.

Lemma cjoin_ichoice_inv_parent : forall A1 B1 A2 B2,
    cjoin (TIChoice A1 B1) (TIChoice A2 B2) ->
    cjoin A1 A2 /\ cjoin B1 B2.
Proof.
  intros A1 B1 A2 B2 [w [H1 H2]].
  destruct (rtc_cstep_ichoice_inv_parent _ _ _ H1)
    as [A1' [B1' [Hw1 [HA1 HB1]]]].
  destruct (rtc_cstep_ichoice_inv_parent _ _ _ H2)
    as [A2' [B2' [Hw2 [HA2 HB2]]]].
  rewrite Hw1 in Hw2. inversion Hw2; subst A2' B2'.
  split; unfold cjoin; eauto.
Qed.


Lemma no_cjoin_iprod_ichoice_parent : forall A B E F,
 ~cjoin(TIProd A B)(TIChoice E F).
Proof.
 intros A B E F [w [H1 H2]].
 destruct(rtc_cstep_iprod_inv_parent _ _ _ H1) as [A' [B' [-> _]]].
 destruct(rtc_cstep_ichoice_inv_parent _ _ _ H2) as [E' [F' [HH _]]].
 discriminate.
Qed.

(* _parent_finish_against_step *)
Definition bounded_progress_parent N := forall t T,
 tsize t <= N -> check [] t T -> value t \/ exists t', step t t'.
Definition erased_dead_step_parent N D := forall xs T X,
 tsize xs <= N -> check [] xs T ->
 cjoin(phi_erase T)(phi_erase(TInterp D X)) -> exists xs',step xs xs'.

Lemma interp_prod_join_parent : forall D X A B,eval D(TIProd A B)->
 cjoin(phi_erase(TInterp D X))
 (phi_erase(TSigma(TInterp A X)(lift 1 0(TInterp B X)))).
Proof.
 intros. apply conv_phi_cjoin. eapply cv_trans.
 - apply cv_interp; [apply conv_of_eval;exact H | apply cv_refl].
 - apply cv_step,st_interp_prod.
Qed.
Lemma interp_choice_join_parent : forall D X E F,eval D(TIChoice E F)->
 cjoin(phi_erase(TInterp D X))
 (phi_erase(TSigma(TEnumT E)(TInterp(TApp(lift 1 0 F)(TVar 0))(lift 1 0 X)))).
Proof.
 intros. apply conv_phi_cjoin. eapply cv_trans.
 - apply cv_interp; [apply conv_of_eval;exact H | apply cv_refl].
 - apply cv_step,st_interp_choice.
Qed.

Lemma against_nil_step_parent : forall N D E F,
 bounded_progress_parent N -> eval D(TIChoice E F) ->eval E TNilE ->
 erased_dead_step_parent N D.
Proof.
 intros N D E F HP HD HE xs T X Hsz HC HJ.
 destruct (HP xs T Hsz HC) as [HV | Hstep]; [|exact Hstep].
 pose proof (cjoin_trans _ _ _ HJ (interp_choice_join_parent D X E F HD)) as HK.
 destruct (erased_sigma_check_value_pair [] xs T HC eq_refl HV _ _ HK)
 as [a [b ->]].
 destruct (erased_pair_interp_choice_origin a b T D X E F HC HJ HD)
 as [TA [TB [HA [HB [HAJ HBJ]]]]].
 assert (Hza:tsize a<=N) by (cbn in Hsz;lia).
 destruct (HP a TA Hza HA) as [HVa | [a' Hstep]].
 - exfalso. eapply (erased_empty_check_value_luna [] a TA HA eq_refl HVa).
   eapply cjoin_trans; [exact HAJ |].
   change (cjoin(phi_erase(TEnumT E))(phi_erase(TEnumT TNilE))).
   apply conv_phi_cjoin,cv_enumt,conv_of_eval,HE.
 - exists(TPair a' b). apply st_pair1,Hstep.
Qed.

Lemma against_prod_left_step_parent : forall N D A B,
 bounded_progress_parent N -> eval D(TIProd A B) ->
 erased_dead_step_parent N A ->erased_dead_step_parent N D.
Proof.
 intros N D A B HP HD IH xs T X Hsz HC HJ.
 destruct (HP xs T Hsz HC) as [HV | Hstep]; [|exact Hstep].
 pose proof (cjoin_trans _ _ _ HJ (interp_prod_join_parent D X A B HD)) as HK.
 destruct (erased_sigma_check_value_pair [] xs T HC eq_refl HV _ _ HK)
 as [a [b ->]].
 destruct (erased_pair_interp_prod_origin a b T D X A B HC HJ HD)
 as [TA [TB [HA [HB [HAJ HBJ]]]]].
 assert (Hza:tsize a<=N) by (cbn in Hsz;lia).
 destruct (IH a TA X Hza HA HAJ) as [a' HS].
 exists(TPair a' b). apply st_pair1,HS.
Qed.
Lemma against_prod_right_step_parent : forall N D A B,
 bounded_progress_parent N -> eval D(TIProd A B) ->
 erased_dead_step_parent N B ->erased_dead_step_parent N D.
Proof.
 intros N D A B HP HD IH xs T X Hsz HC HJ.
 destruct (HP xs T Hsz HC) as [HV | Hstep]; [|exact Hstep].
 pose proof (cjoin_trans _ _ _ HJ (interp_prod_join_parent D X A B HD)) as HK.
 destruct (erased_sigma_check_value_pair [] xs T HC eq_refl HV _ _ HK)
 as [a [b ->]].
 destruct (erased_pair_interp_prod_origin a b T D X A B HC HJ HD)
 as [TA [TB [HA [HB [HAJ HBJ]]]]].
 assert (Hzb:tsize b<=N) by (cbn in Hsz;lia).
 destruct (IH b TB X Hzb HB HBJ) as [b' HS].
 exists(TPair a b'). apply st_pair2,HS.
Qed.

Definition erased_choice_step_parent N E F := forall a b TA TB X,
 tsize(TPair a b)<=N ->check [] a TA ->check [] b TB ->
 cjoin(phi_erase TA)(phi_erase(TEnumT E)) ->
 cjoin(phi_erase TB)(phi_erase(TInterp(TApp F a)X)) ->
 exists p,step(TPair a b)p.

Lemma erased_choice_step_transport_parent : forall N E F E' F',
 erased_choice_step_parent N E F ->
 cjoin(phi_erase E)(phi_erase E') ->cjoin(phi_erase F)(phi_erase F') ->
 erased_choice_step_parent N E' F'.
Proof.
 intros N E F E' F' HC HE HF a b TA TB X Hsz HA HB HJA HJB.
 apply(HC a b TA TB X Hsz HA HB).
 - eapply cjoin_trans;[exact HJA|]. apply cjoin_enumt_parent,cjoin_sym,HE.
 - eapply cjoin_trans;[exact HJB|].
   cbn[phi_erase]. apply cjoin_interp_parent;[|apply cjoin_refl].
   apply cjoin_app_parent;[apply cjoin_sym;exact HF|apply cjoin_refl].
Qed.

Lemma erased_choice_step_eval_transport_parent : forall N D E F,
 erased_choice_step_parent N E F ->eval D(TIChoice E F) ->
 forall E' F',eval D(TIChoice E' F')->erased_choice_step_parent N E' F'.
Proof.
 intros N D E F HC HD E' F' HD'.
 pose proof(conv_phi_cjoin _ _ (conv_of_common_eval _ _ _ HD HD')) as HJ.
 destruct(cjoin_ichoice_inv_parent _ _ _ _ HJ) as [HE HF].
 eapply erased_choice_step_transport_parent;eassumption.
Qed.

Lemma erased_choice_step_to_dead_parent : forall N D E F,
 bounded_progress_parent N ->eval D(TIChoice E F)->
 erased_choice_step_parent N E F ->erased_dead_step_parent N D.
Proof.
 intros N D E F HP HD HK xs T X Hsz HC HJ.
 destruct(HP xs T Hsz HC) as [HV|HS];[|exact HS].
 pose proof(cjoin_trans _ _ _ HJ(interp_choice_join_parent D X E F HD)) as HSigma.
 destruct(erased_sigma_check_value_pair [] xs T HC eq_refl HV _ _ HSigma)
 as [a[b ->]].
 destruct(erased_pair_interp_choice_origin a b T D X E F HC HJ HD)
 as [TA[TB[HA[HB[HAJ HBJ]]]]].
 exact(HK a b TA TB X Hsz HA HB HAJ HBJ).
Qed.

Lemma erased_choice_nil_step_parent : forall N E F,
 bounded_progress_parent N ->eval E TNilE->erased_choice_step_parent N E F.
Proof.
 intros N E F HP HE a b TA TB X Hsz HA HB HJA HJB.
 assert(Hza:tsize a<=N) by(cbn in Hsz;lia).
 destruct(HP a TA Hza HA) as [HV|[a' HS]].
 - exfalso. eapply(erased_empty_check_value_luna [] a TA HA eq_refl HV).
   eapply cjoin_trans;[exact HJA|].
   change(cjoin(phi_erase(TEnumT E))(phi_erase(TEnumT TNilE))).
   apply conv_phi_cjoin,cv_enumt,conv_of_eval,HE.
 - exists(TPair a' b). apply st_pair1,HS.
Qed.

Lemma interp_prod_choice_clash_parent : forall D A B E F,
 eval D(TIProd A B)->eval D(TIChoice E F)->False.
Proof.
 intros. eapply no_cjoin_iprod_ichoice_parent.
 exact(conv_phi_cjoin _ _ (conv_of_common_eval _ _ _ H H0)).
Qed.

Lemma shifted_choice_beta_parent : forall F n,
 conv(TApp(TLam(TApp(lift 1 0 F)(TESucc(TVar 0))))n)
     (TApp F(TESucc n)).
Proof.
 intros F n.
 assert(Hsub:subst n 0(TApp(lift 1 0 F)(TESucc(TVar 0)))=TApp F(TESucc n)).
 { cbn[subst]. rewrite subst_lift_zero,_tmp_commute.lift_zero_id_local.
   reflexivity. }
 rewrite <-Hsub. apply cv_step,st_beta.
Qed.
Lemma pair_step_succ_parent : forall a b p,step(TPair a b)p ->
 exists q,step(TPair(TESucc a)b)q.
Proof.
 intros a b p H;inversion H;subst.
 - eexists. apply st_pair1,st_esucc1;eassumption.
 - eexists. apply st_pair2;eassumption.
Qed.

Lemma erased_choice_cons_step_parent : forall N E F tg E',
 bounded_progress_parent N ->eval E(TConsE tg E') ->
 erased_dead_step_parent N(TApp F TEZero) ->
 erased_choice_step_parent N E' (TLam(TApp(lift 1 0 F)(TESucc(TVar 0)))) ->
 erased_choice_step_parent N E F.
Proof.
 intros N E F tg E' HP HE IH0 IHtail a b TA TB X Hsz HA HB HJA HJB.
 assert(Hza:tsize a<=N) by(cbn in Hsz;lia).
 destruct(HP a TA Hza HA) as [HVa|[a' HS]].
 2:{ exists(TPair a' b). apply st_pair1,HS. }
 destruct(erased_enum_check_value_origin_luna [] a TA HA eq_refl HVa
   (phi_erase E) HJA) as [[tg0[E0[-> HJE]]]|[n[tg0[E0[-> [HN HJE]]]]]].
 - assert(Hzb:tsize b<=N) by(cbn in Hsz;lia).
   destruct(IH0 b TB X Hzb HB HJB) as [b' HS].
   exists(TPair TEZero b'). apply st_pair2,HS.
 - pose proof(cjoin_reduce_right _ _ _ HJE(phi_erase_eval_csteps _ _ HE)) as HJJ.
   destruct(cjoin_conse_inv_parent _ _ _ _ HJJ) as [_ Htail].
   assert(Hzt:tsize(TPair n b)<=N) by(cbn in *;lia).
   assert(HJn:cjoin(phi_erase(TEnumT E0))(phi_erase(TEnumT E'))).
   { apply cjoin_enumt_parent,Htail. }
   assert(HJb:cjoin(phi_erase TB)
    (phi_erase(TInterp(TApp(TLam(TApp(lift 1 0 F)(TESucc(TVar 0))))n)X))).
   { eapply cjoin_trans;[exact HJB|].
     apply conv_phi_cjoin,cv_interp;[apply cv_sym,shifted_choice_beta_parent|apply cv_refl]. }
   destruct(IHtail n b (TEnumT E0) TB X Hzt HN HB HJn HJb) as [p HS].
   eapply pair_step_succ_parent;exact HS.
Qed.

Theorem desc_against_erased_step_mut_parent : forall N,
 bounded_progress_parent N ->forall D,desc_against D ->
 erased_dead_step_parent N D /\
 (forall E F,eval D(TIChoice E F)->erased_choice_step_parent N E F).
Proof.
 intros N HP D HD;induction HD.
 - assert(HC:erased_choice_step_parent N E T).
   { eapply erased_choice_nil_step_parent;eassumption. }
   split.
   + eapply erased_choice_step_to_dead_parent;eassumption.
   + eapply erased_choice_step_eval_transport_parent;eassumption.
 - destruct IHHD as [IH _]. split.
   + eapply against_prod_left_step_parent;eassumption.
   + intros E F HH. exfalso. eapply interp_prod_choice_clash_parent;eassumption.
 - destruct IHHD as [IH _]. split.
   + eapply against_prod_right_step_parent;eassumption.
   + intros E F HH. exfalso. eapply interp_prod_choice_clash_parent;eassumption.
 - destruct IHHD1 as [IH0 _]. destruct IHHD2 as [_ IHtail].
   assert(HC:erased_choice_step_parent N E T).
   { eapply erased_choice_cons_step_parent;[exact HP|exact H0|exact IH0|].
     apply IHtail,ev_refl. }
   split.
   + eapply erased_choice_step_to_dead_parent;eassumption.
   + eapply erased_choice_step_eval_transport_parent;eassumption.
Qed.
Theorem desc_against_erased_step_parent : forall N,
 bounded_progress_parent N ->forall D,desc_against D ->
 erased_dead_step_parent N D.
Proof. intros N HP D HD. exact(proj1(desc_against_erased_step_mut_parent N HP D HD)). Qed.

(* _luna_finish_erased_coverage *)
Lemma pstep_lcons_inv_luna : forall A c L u, pstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ pstep A A' /\ pstep c c' /\ pstep L L'.
Proof. intros A c L u H; inversion H; subst; do 3 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma rtc_pstep_lcons_inv_luna : forall A c L u, rtc pstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ rtc pstep A A' /\ rtc pstep c c' /\ rtc pstep L L'.
Proof.
 intros A c L u H; remember (TLCons A c L) as t eqn:E; revert A c L E.
 induction H; intros; subst; [exists A,c,L; repeat split; apply rtc_refl|].
 destruct (pstep_lcons_inv_luna _ _ _ _ H) as [A1 [c1 [L1 [-> [HA [Hc HL]]]]]].
 destruct (IHrtc A1 c1 L1 eq_refl) as [A2 [c2 [L2 [-> [HA2 [Hc2 HL2]]]]]].
 exists A2,c2,L2; repeat split; eauto using rtc_step.
Qed.
Lemma epstep_lcons_inv_luna : forall A c L u, epstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ epstep A A' /\ epstep c c' /\ epstep L L'.
Proof. intros A c L u H; inversion H; subst; do 3 eexists; repeat split; try reflexivity; eassumption. Qed.
Lemma rtc_epstep_lcons_inv_luna : forall A c L u, rtc epstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ rtc epstep A A' /\ rtc epstep c c' /\ rtc epstep L L'.
Proof.
 intros A c L u H; remember (TLCons A c L) as t eqn:E; revert A c L E.
 induction H; intros; subst; [exists A,c,L; repeat split; apply rtc_refl|].
 destruct (epstep_lcons_inv_luna _ _ _ _ H) as [A1 [c1 [L1 [-> [HA [Hc HL]]]]]].
 destruct (IHrtc A1 c1 L1 eq_refl) as [A2 [c2 [L2 [-> [HA2 [Hc2 HL2]]]]]].
 exists A2,c2,L2; repeat split; eauto using rtc_step.
Qed.
Lemma cstep_lcons_inv_luna : forall A c L u, cstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ cstep A A' /\ cstep c c' /\ cstep L L'.
Proof.
 intros; inversion H; subst.
 - destruct (rtc_pstep_lcons_inv_luna _ _ _ _ H0) as [A' [c' [L' [-> [HA [Hc HL]]]]]].
   exists A',c',L'; repeat split; apply cs_core; assumption.
 - destruct (rtc_epstep_lcons_inv_luna _ _ _ _ H0) as [A' [c' [L' [-> [HA [Hc HL]]]]]].
   exists A',c',L'; repeat split; apply cs_eta; assumption.
Qed.
Lemma rtc_cstep_lcons_inv_luna : forall A c L u, rtc cstep (TLCons A c L) u ->
  exists A' c' L', u = TLCons A' c' L' /\ rtc cstep A A' /\ rtc cstep c c' /\ rtc cstep L L'.
Proof.
 intros A c L u H; remember (TLCons A c L) as t eqn:E; revert A c L E.
 induction H; intros; subst; [exists A,c,L; repeat split; apply rtc_refl|].
 destruct (cstep_lcons_inv_luna _ _ _ _ H) as [A1 [c1 [L1 [-> [HA [Hc HL]]]]]].
 destruct (IHrtc A1 c1 L1 eq_refl) as [A2 [c2 [L2 [-> [HA2 [Hc2 HL2]]]]]].
 exists A2,c2,L2; repeat split; eauto using rtc_step.
Qed.
Lemma cjoin_lcons_inv_erased_luna : forall A c L B d R,
 cjoin (TLCons A c L) (TLCons B d R) -> cjoin A B /\ cjoin c d /\ cjoin L R.
Proof.
 intros A c L B d R [w [H1 H2]].
 destruct (rtc_cstep_lcons_inv_luna _ _ _ _ H1) as [A1 [c1 [L1 [Hw1 [HA1 [Hc1 HL1]]]]]].
 rewrite Hw1 in H2.
 destruct (rtc_cstep_lcons_inv_luna B d R (TLCons A1 c1 L1) H2) as [A2 [c2 [L2 [Hw2 [HA2 [Hc2 HL2]]]]]].
 inversion Hw2; subst A2 c2 L2. repeat split; unfold cjoin; eauto.
Qed.
Lemma pstep_lnil_inv_luna : forall B u, pstep (TLNil B) u ->
  exists B', u = TLNil B' /\ pstep B B'.
Proof. intros B u H; inversion H; subst; eexists; split; try reflexivity; eassumption. Qed.
Lemma rtc_pstep_lnil_inv_luna : forall B u, rtc pstep (TLNil B) u ->
  exists B', u = TLNil B' /\ rtc pstep B B'.
Proof.
 intros B u H; remember (TLNil B) as t eqn:E; revert B E.
 induction H; intros; subst; [exists B; split; [reflexivity|apply rtc_refl]|].
 destruct (pstep_lnil_inv_luna _ _ H) as [B1 [-> HB1]].
 destruct (IHrtc B1 eq_refl) as [B2 [-> HB2]].
 exists B2; split; [reflexivity|eauto using rtc_step].
Qed.
Lemma epstep_lnil_inv_luna : forall B u, epstep (TLNil B) u ->
  exists B', u = TLNil B' /\ epstep B B'.
Proof. intros B u H; inversion H; subst; eexists; split; try reflexivity; eassumption. Qed.
Lemma rtc_epstep_lnil_inv_luna : forall B u, rtc epstep (TLNil B) u ->
  exists B', u = TLNil B' /\ rtc epstep B B'.
Proof.
 intros B u H; remember (TLNil B) as t eqn:E; revert B E.
 induction H; intros; subst; [exists B; split; [reflexivity|apply rtc_refl]|].
 destruct (epstep_lnil_inv_luna _ _ H) as [B1 [-> HB1]].
 destruct (IHrtc B1 eq_refl) as [B2 [-> HB2]].
 exists B2; split; [reflexivity|eauto using rtc_step].
Qed.
Lemma cstep_lnil_inv_luna : forall B u, cstep (TLNil B) u ->
  exists B', u = TLNil B' /\ cstep B B'.
Proof.
 intros B u H; inversion H; subst.
 - destruct (rtc_pstep_lnil_inv_luna _ _ H0) as [B' [-> HB']]; exists B'; split; [reflexivity|apply cs_core; exact HB'].
 - destruct (rtc_epstep_lnil_inv_luna _ _ H0) as [B' [-> HB']]; exists B'; split; [reflexivity|apply cs_eta; exact HB'].
Qed.
Lemma rtc_cstep_lnil_shape : forall B u, rtc cstep (TLNil B) u ->
  exists B', u = TLNil B'.
Proof.
 intros B u H; remember (TLNil B) as t eqn:E; revert B E.
 induction H; intros; subst; [exists B; reflexivity|].
 destruct (cstep_lnil_inv_luna _ _ H) as [B1 [-> HB1]].
 destruct (IHrtc B1 eq_refl) as [B2 ->]. exists B2; reflexivity.
Qed.
Lemma no_cjoin_lcons_lnil_luna : forall A c L B,
  ~ cjoin (TLCons A c L) (TLNil B).
Proof.
 intros A c L B [w [H1 H2]].
 destruct (rtc_cstep_lcons_inv_luna _ _ _ _ H1) as [A1 [c1 [L1 [Hw1 _]]]].
 destruct (rtc_cstep_lnil_shape _ _ H2) as [B' Hw2].
 rewrite Hw1 in Hw2. discriminate Hw2.
Qed.
Lemma erased_spine_covered : forall c L1,
  spine_mem c L1 -> forall L2 bs, covers bs L2 ->
  cjoin (phi_erase L1) (phi_erase L2) ->
  exists d, In d bs /\ cjoin (phi_erase c) (phi_erase d).
Proof.
  intros c L1 Hmem.
  induction Hmem as [Phi A c' Phi' Heval Hcc | Phi A c' Phi' Heval Htail IH];
    intros L2 bs Hcov Hjoin.
  - pose proof (phi_erase_eval_csteps _ _ Heval) as Hleft.
    destruct (cjoin_reduce_left _ _ _ Hjoin Hleft) as [w [Hw1 Hw2]].
    inversion Hcov; subst.
    + exfalso.
      pose proof (phi_erase_eval_csteps _ _ H) as Hright.
      destruct (cjoin_reduce_right _ _ _ (ex_intro _ w (conj Hw1 Hw2)) Hright) as [z [Hz1 Hz2]].
      cbn in Hz1, Hz2.
      apply (no_cjoin_lcons_lnil_luna (phi_erase A) (phi_erase c')
        (phi_erase Phi') (phi_erase A0)).
      exact (ex_intro _ z (conj Hz1 Hz2)).
    + pose proof (phi_erase_eval_csteps _ _ H) as Hright.
      destruct (cjoin_reduce_right _ _ _ (ex_intro _ w (conj Hw1 Hw2)) Hright)
        as [z [Hz1 Hz2]].
      destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ (ex_intro _ z (conj Hz1 Hz2)))
        as [_ [Hcd _]].
      apply Exists_exists in H0. destruct H0 as [d [Hd Hconv]].
      exists d; split; [exact Hd|].
      eapply cjoin_trans; [apply conv_phi_cjoin; exact Hcc|].
      eapply cjoin_trans; [exact Hcd|].
      apply conv_phi_cjoin; exact Hconv.
  - pose proof (phi_erase_eval_csteps _ _ Heval) as Hleft.
    destruct (cjoin_reduce_left _ _ _ Hjoin Hleft) as [w [Hw1 Hw2]].
    inversion Hcov; subst.
    + exfalso.
      pose proof (phi_erase_eval_csteps _ _ H) as Hright.
      destruct (cjoin_reduce_right _ _ _ (ex_intro _ w (conj Hw1 Hw2)) Hright) as [z [Hz1 Hz2]].
      cbn in Hz1, Hz2.
      apply (no_cjoin_lcons_lnil_luna (phi_erase A) (phi_erase c')
        (phi_erase Phi') (phi_erase A0)).
      exact (ex_intro _ z (conj Hz1 Hz2)).
    + pose proof (phi_erase_eval_csteps _ _ H) as Hright.
      destruct (cjoin_reduce_right _ _ _ (ex_intro _ w (conj Hw1 Hw2)) Hright)
        as [z [Hz1 Hz2]].
      destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ (ex_intro _ z (conj Hz1 Hz2)))
        as [_ [_ Htailjoin]].
      eapply IH; eassumption.
Qed.

Lemma erased_spine_covered_pos : forall c n L1 L2 bs,
  enum_pos c n ->
  Forall (fun d => exists m, enum_pos d m) bs ->
  spine_mem c L1 -> covers bs L2 -> conv L1 L2 ->
  exists d, In d bs /\ enum_pos d n.
Proof.
  intros c n L1 L2 bs Hc Hbs Hmem Hcov Hconv.
  destruct (erased_spine_covered c L1 Hmem L2 bs Hcov
      (conv_phi_cjoin _ _ Hconv)) as [d [Hd Hcd]].
  rewrite Forall_forall in Hbs.
  destruct (Hbs d Hd) as [m Hdm].
  pose proof (phi_erase_enum_pos _ _ Hc) as Hec.
  pose proof (phi_erase_enum_pos _ _ Hdm) as Hed.
  destruct Hcd as [w [Hcw Hdw]].
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hcw Hec) as Hwc.
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hdw Hed) as Hwd.
  subst w.
  exists d. split; [exact Hd|].
  assert (Hmn : m = n).
  { eapply enum_pos_functional; [exact Hed |].
    rewrite <- Hwd. exact Hec. }
  subst m. exact Hdm.
Qed.

(* _luna_finish_musapp_cjoin *)
Lemma pstep_mus_inv_luna : forall S u, pstep (TMuS S) u ->
  exists S', u = TMuS S' /\ pstep S S'.
Proof. intros; inversion H; subst; eexists; split; [reflexivity|eassumption]. Qed.
Lemma epstep_mus_inv_luna : forall S u, epstep (TMuS S) u ->
  exists S', u = TMuS S' /\ epstep S S'.
Proof. intros; inversion H; subst; eexists; split; [reflexivity|eassumption]. Qed.

Lemma pstep_musapp_inv_luna : forall S i u, pstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ pstep S S' /\ pstep i i'.
Proof. intros S i u H; inversion H; subst.
  destruct (pstep_mus_inv_luna _ _ H2) as [S' [-> HS']].
  exists S', a'. repeat split; assumption. Qed.
Lemma rtc_pstep_musapp_inv_luna : forall S i u, rtc pstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ rtc pstep S S' /\ rtc pstep i i'.
Proof.
 intros S i u H; remember (TApp (TMuS S) i) as t eqn:E; revert S i E.
 induction H; intros; subst; [exists S,i; repeat split; apply rtc_refl|].
 destruct (pstep_musapp_inv_luna _ _ _ H) as [S1 [i1 [-> [HS Hi]]]].
 destruct (IHrtc S1 i1 eq_refl) as [S2 [i2 [-> [HS2 Hi2]]]].
 exists S2,i2; repeat split; eauto using rtc_step.
Qed.
Lemma epstep_musapp_inv_luna : forall S i u, epstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ epstep S S' /\ epstep i i'.
Proof. intros S i u H; inversion H; subst.
  destruct (epstep_mus_inv_luna _ _ H2) as [S' [-> HS']].
  exists S', a'. repeat split; assumption. Qed.
Lemma rtc_epstep_musapp_inv_luna : forall S i u, rtc epstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ rtc epstep S S' /\ rtc epstep i i'.
Proof.
 intros S i u H; remember (TApp (TMuS S) i) as t eqn:E; revert S i E.
 induction H; intros; subst; [exists S,i; repeat split; apply rtc_refl|].
 destruct (epstep_musapp_inv_luna _ _ _ H) as [S1 [i1 [-> [HS Hi]]]].
 destruct (IHrtc S1 i1 eq_refl) as [S2 [i2 [-> [HS2 Hi2]]]].
 exists S2,i2; repeat split; eauto using rtc_step.
Qed.
Lemma cstep_musapp_inv_luna : forall S i u, cstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ cstep S S' /\ cstep i i'.
Proof.
 intros S i u H; inversion H; subst.
 - destruct (rtc_pstep_musapp_inv_luna _ _ _ H0) as [S' [i' [-> [HS Hi]]]].
   exists S',i'; repeat split; apply cs_core; assumption.
 - destruct (rtc_epstep_musapp_inv_luna _ _ _ H0) as [S' [i' [-> [HS Hi]]]].
   exists S',i'; repeat split; apply cs_eta; assumption.
Qed.
Lemma rtc_cstep_musapp_inv_luna : forall S i u, rtc cstep (TApp (TMuS S) i) u ->
  exists S' i', u = TApp (TMuS S') i' /\ rtc cstep S S' /\ rtc cstep i i'.
Proof.
 intros S i u H; remember (TApp (TMuS S) i) as t eqn:E; revert S i E.
 induction H; intros; subst; [exists S,i; repeat split; apply rtc_refl|].
 destruct (cstep_musapp_inv_luna _ _ _ H) as [S1 [i1 [-> [HS Hi]]]].
 destruct (IHrtc S1 i1 eq_refl) as [S2 [i2 [-> [HS2 Hi2]]]].
 exists S2,i2; repeat split; eauto using rtc_step.
Qed.
Lemma cjoin_musapp_inv_luna : forall S1 S2 i1 i2,
  cjoin (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
  cjoin S1 S2 /\ cjoin i1 i2.
Proof.
 intros S1 S2 i1 i2 [w [H1 H2]].
 destruct (rtc_cstep_musapp_inv_luna _ _ _ H1) as [S1' [i1' [Hw1 [HS1 Hi1]]]].
 rewrite Hw1 in H2.
 destruct (rtc_cstep_musapp_inv_luna _ _ _ H2) as [S2' [i2' [Hw2 [HS2 Hi2]]]].
 inversion Hw2; subst S2' i2'. repeat split; unfold cjoin; eauto.
Qed.

(* _luna_finish_branch_erase_bridge *)
Lemma phi_branch_erase_bridge_luna : forall t,
    phi_erase (branch_erase t) = phi_erase t.
Proof.
  apply (tsize_strong_ind (fun t =>
    phi_erase (branch_erase t) = phi_erase t)).
  intros t IH. destruct t; cbn [branch_erase phi_erase].
  all: repeat match goal with
  | |- context [phi_erase (branch_erase ?x)] =>
      rewrite (IH x ltac:(cbn; lia))
  end; try reflexivity.
  - rewrite map_map. f_equal.
    apply map_ext_in. intros [c b] Hin. cbn.
    rewrite (IH c ltac:(eapply tsize_case_bs; exact Hin)).
    rewrite (IH b ltac:(eapply tsize_case_bs_body; exact Hin)).
    reflexivity.
Qed.

Lemma epstep_conv_bridge_mut :
    (forall t u, epstep t u -> conv t u) /\
    (forall bs bs', epbranches bs bs' -> forall pre M Q,
      conv (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply epstep_epbranches_ind; intros;
    try solve [eauto 12 using cv_refl, cv_pi, cv_lam, cv_app, cv_sigma,
      cv_pair, cv_fst, cv_snd, cv_conse, cv_enumt, cv_esucc, cv_epi,
      cv_switch, cv_idesc, cv_ivar, cv_iprod, cv_ipi, cv_isig, cv_ichoice,
      cv_interp, cv_mui, cv_mus, cv_in, cv_ind, cv_iall, cv_hyps,
      cv_list, cv_lnil, cv_lcons].
  - eapply cv_trans; [apply (H1 [] M Q) | apply cv_case; [exact H | exact H0]].
  - eapply cv_trans; [apply cv_eta | assumption].
  - eapply cv_trans; [apply cv_case_br; [exact H | exact H0] |].
    specialize (H1 (pre ++ [(c',b')]) M Q).
    repeat rewrite <- app_assoc in H1. cbn in H1. exact H1.
Qed.

Lemma epstep_conv_bridge : forall t u, epstep t u -> conv t u.
Proof. exact (proj1 epstep_conv_bridge_mut). Qed.

Lemma rtc_pstep_conv_bridge : forall t u, rtc pstep t u -> conv t u.
Proof. intros t u H; induction H; [apply cv_refl|eapply cv_trans; [apply pstep_conv; exact H|exact IHrtc]]. Qed.

Lemma rtc_epstep_conv_bridge : forall t u, rtc epstep t u -> conv t u.
Proof. intros t u H; induction H; [apply cv_refl|eapply cv_trans; [apply epstep_conv_bridge; exact H|exact IHrtc]]. Qed.

Lemma cstep_conv_bridge : forall t u, cstep t u -> conv t u.
Proof. intros t u H; destruct H as [x y Hp|x y He]; [apply rtc_pstep_conv_bridge; exact Hp|apply rtc_epstep_conv_bridge; exact He]. Qed.

Lemma rtc_cstep_conv_bridge : forall t u, rtc cstep t u -> conv t u.
Proof. intros t u H; induction H; [apply cv_refl|eapply cv_trans; [apply cstep_conv_bridge; exact H|exact IHrtc]]. Qed.

Lemma cjoin_conv_bridge : forall t u, cjoin t u -> conv t u.
Proof. intros t u [w [H1 H2]]; eapply cv_trans; [apply rtc_cstep_conv_bridge; exact H1|apply cv_sym; apply rtc_cstep_conv_bridge; exact H2]. Qed.

Lemma cjoin_branch_to_phi_luna : forall t u,
    cjoin (branch_erase t) (branch_erase u) ->
    cjoin (phi_erase t) (phi_erase u).
Proof.
  intros t u H.
  pose proof (cjoin_conv_bridge _ _ H) as Hconv.
  pose proof (conv_phi_cjoin _ _ Hconv) as Hphi.
  rewrite (phi_branch_erase_bridge_luna t) in Hphi.
  rewrite (phi_branch_erase_bridge_luna u) in Hphi.
  exact Hphi.
Qed.

(* _luna_finish_mus_branch_transport *)
Lemma mus_branch_transport_luna : forall S1 S2 i1 i2 c,
    conv (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) ->
    cjoin (phi_erase (TApp (branches (TApp S1 i1)) c))
      (phi_erase (TApp (branches (TApp S2 i2)) c)).
Proof.
  intros S1 S2 i1 i2 c Hconv.
  pose proof (branch_erase_conv
    (TApp (TMuS S1) i1) (TApp (TMuS S2) i2) Hconv) as Hfc.
  pose proof (fconv_cjoin _ _ Hfc) as Hbranch.
  cbn [branch_erase branches] in Hbranch.
  destruct (cjoin_musapp_inv_luna
    (TLam (TFst (TApp (lift 1 0 (branch_erase S1)) (TVar 0))))
    (TLam (TFst (TApp (lift 1 0 (branch_erase S2)) (TVar 0))))
    (branch_erase i1) (branch_erase i2) Hbranch) as [HS Hi].
  pose proof (cjoin_app_parent _ _ _ _ HS Hi) as Happ.
  (* Contract the two erased MuS wrappers at the application head. *)
  assert (Hleft0 : rtc cstep
      (TApp (TLam (TFst (TApp (lift 1 0 (branch_erase S1)) (TVar 0))))
        (branch_erase i1))
      (subst (branch_erase i1) 0
        (TFst (TApp (lift 1 0 (branch_erase S1)) (TVar 0))))).
  { eapply rtc_step; [apply pstep_cstep; apply ps_beta; apply pstep_refl; apply pstep_refl | apply rtc_refl]. }
  assert (Hleft : rtc cstep
      (TApp (TLam (TFst (TApp (lift 1 0 (branch_erase S1)) (TVar 0))))
        (branch_erase i1))
      (TFst (TApp (branch_erase S1) (branch_erase i1)))).
  { cbn [subst lift] in Hleft0.
    rewrite PeanoNat.Nat.ltb_irrefl, PeanoNat.Nat.eqb_refl in Hleft0.
    rewrite _tmp_commute.lift_zero_id_local in Hleft0.
    rewrite subst_lift_zero in Hleft0. exact Hleft0. }
  assert (Hright0 : rtc cstep
      (TApp (TLam (TFst (TApp (lift 1 0 (branch_erase S2)) (TVar 0))))
        (branch_erase i2))
      (subst (branch_erase i2) 0
        (TFst (TApp (lift 1 0 (branch_erase S2)) (TVar 0))))).
  { eapply rtc_step; [apply pstep_cstep; apply ps_beta; apply pstep_refl; apply pstep_refl | apply rtc_refl]. }
  assert (Hright : rtc cstep
      (TApp (TLam (TFst (TApp (lift 1 0 (branch_erase S2)) (TVar 0))))
        (branch_erase i2))
      (TFst (TApp (branch_erase S2) (branch_erase i2)))).
  { cbn [subst lift] in Hright0.
    rewrite PeanoNat.Nat.ltb_irrefl, PeanoNat.Nat.eqb_refl in Hright0.
    rewrite _tmp_commute.lift_zero_id_local in Hright0.
    rewrite subst_lift_zero in Hright0. exact Hright0. }
  pose proof (cjoin_reduce_left _ _ _ Happ Hleft) as Hred1.
  pose proof (cjoin_reduce_right _ _ _ Hred1 Hright) as Hred2.
  apply cjoin_branch_to_phi_luna.
  apply cjoin_app_parent; [exact Hred2 | apply cjoin_refl].
Qed.

(* The former direct phi-spine progress bridge below depended on transporting
   weak-head list membership across full parallel joins.  It is obsolete in
   the no-Eq-phi calculus; signature transport now uses [joined_mem] below.
(* _luna_finish_prune_mem_or *)
Lemma spine_phi_mem_direct_or_luna : forall c Phi,
    spine_mem c Phi -> forall S i Psi (P : Prop),
    spine_phi S i Phi Psi ->
    (forall d, conv c d ->
      desc_against (TApp (branches (TApp S i)) d) -> P) ->
    spine_mem c Psi \/ P.
Proof.
  intros c Phi Hmem.
  induction Hmem as [Phi A c' Phi' Heval Hcc | Phi A c' Phi' Heval Htail IH];
    intros S i Psi P Hphi HP;
    pose proof (pjoin_eval_left _ _ _ (pjoin_refl Phi) Heval) as Hleft;
    inversion Hphi; subst.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [Hlabels _]].
    left. eapply sm_here; [apply ev_refl |].
    eapply cv_trans; [exact Hcc | apply pjoin_conv; exact Hlabels].
  - right. eapply HP; [|exact H0].
    pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [Hlabels _]].
    eapply cv_trans; [exact Hcc | apply pjoin_conv; exact Hlabels].
  - left. eapply sm_here; eassumption.
  - exfalso. eapply no_pjoin_lcons_lnil.
    eapply pjoin_eval_right; eassumption.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [_ Htails]].
    destruct (IH S i _ P ltac:(eassumption) HP) as [Hm | Hp].
    + left. eapply sm_there; [apply ev_refl | exact Hm].
    + right; exact Hp.
  - pose proof (pjoin_eval_right _ _ _ Hleft H) as Hboth.
    destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [_ Htails]].
    destruct (IH S i _ P ltac:(eassumption) HP) as [Hm | Hp].
    + left; exact Hm.
    + right; exact Hp.
  - left. eapply sm_there; eassumption.
Qed.

Lemma spine_phi_mem_or_luna : forall S i Phi Psi c,
    spine_phi S i Phi Psi -> spine_mem c Phi -> forall P : Prop,
    (forall d, conv c d ->
      desc_against (TApp (branches (TApp S i)) d) -> P) ->
    spine_mem c Psi \/ P.
Proof.
  intros; eapply spine_phi_mem_direct_or_luna; eauto.
Qed.

(* _luna_finish_pruned_coverage *)
Lemma no_pjoin_lnil_neutral_luna : forall A n,
  neutral n -> ~ pjoin (TLNil A) n.
Proof.
  intros A n Hn [w [HL HN]].
  destruct (psteps_lnil_inv _ _ HL) as [A' [Hw _]].
  pose proof (luna_neutral_psteps n Hn w HN) as HH.
  rewrite Hw in HH. inversion HH.
Qed.

Lemma spine_phi_covers_join : forall S i L1 L3,
  spine_phi S i L1 L3 -> forall L2 bs, covers bs L2 ->
  pjoin L1 L2 -> covers bs L3.
Proof.
  intros S i L1 L3 Hphi. induction Hphi; intros L2 bs Hcov Hjoin.
  - apply cov_nil with (A:=A). apply ev_refl.
  - pose proof (pjoin_eval_left _ _ _ Hjoin H) as Hleft.
    inversion Hcov; subst.
    + exfalso. eapply no_pjoin_lcons_lnil; eapply pjoin_eval_right; eassumption.
    + pose proof (pjoin_eval_right _ _ _ Hleft H0) as Hboth.
      destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [Hheads Htails]].
      apply cov_cons with (Phi:=TLCons A c Psi') (A:=A) (c:=c) (Phi':=Psi'); [apply ev_refl| |].
      * apply Exists_exists in H1. destruct H1 as [d [Hd Hcd]].
        apply Exists_exists. exists d. split; [exact Hd|].
        eapply cv_trans; [apply pjoin_conv; exact Hheads|exact Hcd].
      * eapply IHHphi; eassumption.
  - pose proof (pjoin_eval_left _ _ _ Hjoin H) as Hleft.
    inversion Hcov; subst.
    + exfalso. eapply no_pjoin_lcons_lnil; eapply pjoin_eval_right; eassumption.
    + pose proof (pjoin_eval_right _ _ _ Hleft H1) as Hboth.
      destruct (pjoin_lcons_inv _ _ _ _ _ _ Hboth) as [_ [_ Htails]].
      eapply IHHphi; eassumption.
  - pose proof (pjoin_eval_left _ _ _ Hjoin H) as Hleft.
    inversion Hcov; subst.
    + exfalso.
      pose proof (pjoin_eval_right _ _ _ Hleft H1) as Hboth.
      apply (no_pjoin_lnil_neutral_luna A Phin H0).
      apply pjoin_sym; exact Hboth.
    + exfalso. eapply luna_no_pjoin_lcons_neutral; [exact H0|].
      pose proof (pjoin_eval_right _ _ _ Hleft H1) as Hboth.
      apply pjoin_sym; exact Hboth.
Qed.

Lemma spine_phi_covers : forall S i Phi Psi bs,
  spine_phi S i Phi Psi -> covers bs Phi -> covers bs Psi.
Proof. intros; eapply spine_phi_covers_join; eauto using pjoin_refl. Qed.

(* _parent_finish_phi_step *)
Lemma converted_branch_dead_payload_steps_parent : forall N S0 i0 S1 i1 c d xs X,
 bounded_progress_parent N ->tsize xs<=N ->
 check [] xs(TInterp(TApp(branches(TApp S0 i0))c)X) ->
 conv(TApp(TMuS S0)i0)(TApp(TMuS S1)i1) ->
 cjoin(phi_erase c)(phi_erase d) ->
 desc_against(TApp(branches(TApp S1 i1))d) ->
 exists xs',step xs xs'.
Proof.
 intros N S0 i0 S1 i1 c d xs X HP Hsz HC Hconv Hcd HD.
 eapply(desc_against_erased_step_parent N HP _ HD xs _ X Hsz HC).
 cbn[phi_erase]. apply cjoin_interp_parent;[|apply cjoin_refl].
 eapply cjoin_trans.
 - exact(mus_branch_transport_luna S0 S1 i0 i1 c Hconv).
 - apply cjoin_app_parent;[apply cjoin_refl|exact Hcd].
Qed.

Theorem direct_phi_spine_progress_parent : forall N S0 i0 S1 S2 i c n xs X
 Phi1 Phi2 Psi1 Psi2 bs,
 bounded_progress_parent N ->tsize xs<=N ->
 check [] xs(TInterp(TApp(branches(TApp S0 i0))c)X) ->
 conv(TApp(TMuS S0)i0)(TApp(TMuS S1)i) ->
 enum_pos c n ->Forall(fun d=>exists m,enum_pos d m)bs ->
 spine_mem c Phi1 ->spine_phi S1 i Phi1 Psi1 ->
 spine_phi S2 i Phi2 Psi2 ->conv Psi1 Psi2 ->covers bs Phi2 ->
 (exists d,In d bs /\enum_pos d n) \/exists xs',step xs xs'.
Proof.
 intros N S0 i0 S1 S2 i c n xs X Phi1 Phi2 Psi1 Psi2 bs
 HP Hsz HC Hconv Hpos Hbs Hmem Hphi1 Hphi2 Hpsi Hcov.
 destruct(spine_phi_mem_or_luna S1 i Phi1 Psi1 c Hphi1 Hmem
  (exists xs',step xs xs')) as [HM|HS].
 - intros d Hcd HD.
   eapply converted_branch_dead_payload_steps_parent;
     [exact HP|exact Hsz|exact HC|exact Hconv|apply conv_phi_cjoin;exact Hcd|exact HD].
 - left. eapply erased_spine_covered_pos;
     [exact Hpos|exact Hbs|exact HM| |exact Hpsi].
   eapply spine_phi_covers;eassumption.
 - right. exact HS.
Qed.
*)
End SignatureConversion.

(* Checked signature-transport component: SignatureInstances. *)
Module SignatureInstances.
(* Translation of signature applications to explicit instances.
   This is proof infrastructure; the source typing and conversion rules are unchanged. *)
Import SignatureConversion ErasureCounterexample.
Import ListNotations TypeRulesCore _tmp_epstep
 _tmp_epstep_subst _tmp_commute
 _work_mixed_closure _work_cjoin
 _work_cstep_invariants _work_conv_whd_pos
 _luna_phi_erase_shapes MuApplicationSort.

Fixpoint instance_translate (t : term) : term :=
  match t with
  | TVar n => TVar n | TSort k => TSort k
  | TPi A B => TPi (instance_translate A) (instance_translate B)
  | TLam b => TLam (instance_translate b)
  | TApp f a => TApp (instance_translate f) (instance_translate a)
  | TSigma A B => TSigma (instance_translate A) (instance_translate B)
  | TPair a b => TPair (instance_translate a) (instance_translate b)
  | TFst p => TFst (instance_translate p) | TSnd p => TSnd (instance_translate p)
  | TUnitT => TUnitT | TUnit => TUnit | TUId => TUId | TTag s => TTag s
  | TEnumU => TEnumU | TNilE => TNilE
  | TConsE t E => TConsE (instance_translate t) (instance_translate E)
  | TEnumT E => TEnumT (instance_translate E)
  | TEZero => TEZero | TESucc n => TESucc (instance_translate n)
  | TEPi E P => TEPi (instance_translate E) (instance_translate P)
  | TSwitch E P p e =>
      TSwitch (instance_translate E) (instance_translate P) (instance_translate p) (instance_translate e)
  | TIDesc IT => TIDesc (instance_translate IT) | TIVar i => TIVar (instance_translate i)
  | TI1 => TI1
  | TIProd A B => TIProd (instance_translate A) (instance_translate B)
  | TIPi Sd T => TIPi (instance_translate Sd) (instance_translate T)
  | TISig Sd T => TISig (instance_translate Sd) (instance_translate T)
  | TIChoice E T => TIChoice (instance_translate E) (instance_translate T)
  | TInterp D X => TInterp (instance_translate D) (instance_translate X)
  | TMuI R => TMuI (instance_translate R)
  | TMuS Sf => TLam (TApp (TMuS (TPair
        (TFst (TApp (lift 1 0 (instance_translate Sf)) (TVar 0)))
        (TSnd (TApp (lift 1 0 (instance_translate Sf)) (TVar 0))))) (TVar 0))
  | TIn x => TIn (instance_translate x)
  | TInd R P stp i x =>
      TInd (instance_translate R) (instance_translate P) (instance_translate stp)
           (instance_translate i) (instance_translate x)
  | TIAll D X xs P =>
      TIAll (instance_translate D) (instance_translate X) (instance_translate xs) (instance_translate P)
  | THyps D X P h xs =>
      THyps (instance_translate D) (instance_translate X) (instance_translate P)
            (instance_translate h) (instance_translate xs)
  | TList A => TList (instance_translate A)
  | TLNil A => TLNil (instance_translate A)
  | TLCons A a l => TLCons (instance_translate A) (instance_translate a) (instance_translate l)
  | TCase M Q bs =>
      TCase (instance_translate M) (instance_translate Q)
        (map (fun '(c,b) => (instance_translate c, instance_translate b)) bs)
  end.
Lemma instance_translate_lift : forall t d k,
    instance_translate (lift d k t) = lift d k (instance_translate t).
Proof.
  assert (Hmap : forall bs d k,
      (forall c b, In (c,b) bs ->
       instance_translate (lift d k c) = lift d k (instance_translate c) /\
       instance_translate (lift d (S k) b) = lift d (S k) (instance_translate b)) ->
      map (fun '(c,b) => (instance_translate c, instance_translate b))
          (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs) =
      map (fun '(c,b) => (lift d k c, lift d (S k) b))
          (map (fun '(c,b) => (instance_translate c, instance_translate b)) bs)).
  {
    intros bs d k H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity|].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall d k,
    instance_translate (lift d k t) = lift d k (instance_translate t))).
  intros t IH d k. destruct t; cbn.
  all: try solve [destruct k as [|k]; cbn; [reflexivity |];
                  destruct (Nat.leb n k); reflexivity].
  all: try solve [repeat f_equal; try reflexivity;
    try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia)].
  all: try (apply f_equal3).
  all: try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia).
  all: try solve [
    rewrite (IH t ltac:(cbn; lia) d k);
    rewrite lift_lift_one_zero; reflexivity ].
  all: apply Hmap; intros c b Hin; split;
    [ apply IH; eapply tsize_case_bs; exact Hin
    | apply IH; eapply tsize_case_bs_body; exact Hin ].
Qed.


Lemma instance_translate_subst : forall t u k,
    instance_translate (subst u k t) = subst (instance_translate u) k (instance_translate t).
Proof.
  assert (Hmap : forall bs u k,
      (forall c b, In (c,b) bs ->
       instance_translate (subst u k c) = subst (instance_translate u) k (instance_translate c) /\
       instance_translate (subst u (S k) b) =
         subst (instance_translate u) (S k) (instance_translate b)) ->
      map (fun '(c,b) => (instance_translate c, instance_translate b))
          (map (fun '(c,b) => (subst u k c, subst u (S k) b)) bs) =
      map (fun '(c,b) =>
             (subst (instance_translate u) k c,
              subst (instance_translate u) (S k) b))
          (map (fun '(c,b) => (instance_translate c, instance_translate b)) bs)).
  {
    intros bs u k H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity|].
    f_equal. f_equal.
    - exact (proj1 (H c b (or_introl eq_refl))).
    - exact (proj2 (H c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply H. right; exact Hin.
  }
  apply (tsize_strong_ind (fun t => forall u k,
    instance_translate (subst u k t) = subst (instance_translate u) k (instance_translate t))).
  intros t IH u k. destruct t; cbn.
  all: try solve [destruct k as [|k]; cbn;
    [ destruct n; cbn; try reflexivity;
      rewrite instance_translate_lift; reflexivity
    | destruct (Nat.leb n k); cbn; try reflexivity;
      destruct (Nat.eqb n (S k)); cbn; try reflexivity;
      rewrite instance_translate_lift; reflexivity ]].
  all: try (f_equal; try reflexivity;
    try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia)).
  all: try (apply f_equal3).
  all: try (apply IH; try (pose proof (tsize_pos t1));
                    try (pose proof (tsize_pos t2)); cbn; lia).
  all: try solve [
    rewrite (IH t ltac:(cbn; lia) u k);
    rewrite subst_lift_one_zero; reflexivity ].
  all: apply Hmap; intros c b Hin; split;
    [ apply IH; eapply tsize_case_bs; exact Hin
    | apply IH; eapply tsize_case_bs_body; exact Hin ].
Qed.


Import ListNotations TypeRulesCore.

Lemma instance_translate_enum_pos : forall c n, enum_pos c n ->
    enum_pos (instance_translate c) n.
Proof. intros c n H. induction H; cbn; constructor; assumption. Qed.

Lemma instance_translate_nth_error : forall bs k c b,
    nth_error bs k = Some (c,b) ->
    nth_error (map (fun '(c,b) => (instance_translate c, instance_translate b)) bs) k =
      Some (instance_translate c, instance_translate b).
Proof.
  intros bs k. revert k.
  induction bs as [|[c0 b0] bs IH]; intros [|k] c b H;
    cbn in *; try discriminate.
  - inversion H; reflexivity.
  - apply IH; exact H.
Qed.

Lemma instance_translate_nth_inv : forall bs k c b,
    nth_error (map (fun '(c,b) => (instance_translate c, instance_translate b)) bs) k =
      Some (c,b) ->
    exists c0 b0, nth_error bs k = Some (c0,b0) /\
      instance_translate c0 = c /\ instance_translate b0 = b.
Proof.
  intros bs k. revert k.
  induction bs as [|[c0 b0] bs IH];
    intros [|k] c b H; cbn in *; try discriminate.
  - inversion H; subst. eexists; eexists; repeat split; reflexivity.
  - destruct (IH k c b H) as [c1 [b1 [H1 [H2 H3]]]].
    exists c1, b1. repeat split; cbn; assumption.
Qed.

Lemma instance_translate_step : forall t u,
    step t u -> step (instance_translate t) (instance_translate u).
Proof.
  intros t u H; induction H.
  all: cbn; try constructor; eauto.
  - rewrite instance_translate_subst. apply st_beta.
  - repeat rewrite instance_translate_lift. apply st_epi_cons.
  - repeat rewrite instance_translate_lift. apply st_switch_succ.
  - repeat rewrite instance_translate_lift. apply st_interp_prod.
  - repeat rewrite instance_translate_lift. apply st_interp_pi.
  - repeat rewrite instance_translate_lift. apply st_interp_sig.
  - repeat rewrite instance_translate_lift. apply st_interp_choice.
  - repeat rewrite instance_translate_lift. apply st_iall_prod.
  - repeat rewrite instance_translate_lift. apply st_iall_pi.
  - repeat rewrite instance_translate_lift. apply st_hyps_pi.
  - repeat rewrite instance_translate_lift. apply st_ind.
  - rewrite instance_translate_subst.
    apply st_case with
      (a := instance_translate a) (xs := instance_translate xs) (Q := instance_translate Q)
      (bs := map (fun '(c,b) => (instance_translate c, instance_translate b)) bs)
      (k := k) (c := instance_translate c) (b := instance_translate b) (n := n).
    + apply instance_translate_nth_error. exact H.
    + apply instance_translate_enum_pos. exact H0.
    + apply instance_translate_enum_pos. exact H1.
    + intros j cj bj Hj Hnth.
      destruct (instance_translate_nth_inv _ _ _ _ Hnth)
        as [cj0 [bj0 [Hsrc [Hc Hb]]]].
      destruct (H2 j cj0 bj0 Hj Hsrc) as [nj [Hpos Hneq]].
      exists nj. split.
      * rewrite <- Hc. apply instance_translate_enum_pos. exact Hpos.
      * exact Hneq.
  - repeat rewrite map_app. cbn.
    apply st_case_lbl. exact IHstep.
Qed.


Ltac instance_fconv_context :=
  match goal with
  | IH : fconv ?a ?b |- fconv ?l ?r =>
    let p := eval pattern a in l in
    lazymatch p with
    | ?F _ => apply (fconv_map F);
        [intros; constructor; assumption | exact IH]
    end
  end.

Lemma instance_translate_fstep : forall t u, fstep t u ->
  fconv (instance_translate t) (instance_translate u).
Proof.
  intros t u H. induction H; cbn;
    try solve [apply fc_step, fs_step, instance_translate_step; assumption];
    try solve [rewrite instance_translate_lift; apply fc_step, fs_eta];
    try solve [instance_fconv_context];
    try solve [repeat rewrite map_app; cbn; instance_fconv_context].
  apply (fconv_map TLam); [intros; apply fs_lam; assumption |].
  apply (fconv_map (fun z => TApp z (TVar 0)));
    [intros; apply fs_app1; assumption |].
  apply (fconv_map TMuS); [intros; apply fs_mus; assumption |].
  apply fconv_pair.
  - apply (fconv_map TFst); [intros; apply fs_fst; assumption |].
    apply (fconv_map (fun z => TApp z (TVar 0)));
      [intros; apply fs_app1; assumption |].
    apply fconv_lift_parent. exact IHfstep.
  - apply (fconv_map TSnd); [intros; apply fs_snd; assumption |].
    apply (fconv_map (fun z => TApp z (TVar 0)));
      [intros; apply fs_app1; assumption |].
    apply fconv_lift_parent. exact IHfstep.
Qed.

Theorem instance_translate_fconv : forall t u, fconv t u ->
  fconv (instance_translate t) (instance_translate u).
Proof.
  intros t u H. induction H; eauto using fconv, instance_translate_fstep.
Qed.

Definition signature_instance (B L i : term) : term :=
  TApp (TMuS (TPair B L)) i.

Lemma instance_translate_musapp : forall Sf i,
  step (instance_translate (TApp (TMuS Sf) i))
    (signature_instance
      (branches (TApp (instance_translate Sf) (instance_translate i)))
      (labels (TApp (instance_translate Sf) (instance_translate i)))
      (instance_translate i)).
Proof.
  intros Sf i. cbn [instance_translate].
  pose proof (st_beta
    (TApp
      (TMuS (TPair
        (TFst (TApp (lift 1 0 (instance_translate Sf)) (TVar 0)))
        (TSnd (TApp (lift 1 0 (instance_translate Sf)) (TVar 0)))))
      (TVar 0)) (instance_translate i)) as H.
  cbn [subst] in H. rewrite subst_lift_zero in H.
  rewrite _tmp_commute.lift_zero_id_local in H.
  exact H.
Qed.

Theorem instance_translate_erased_eta : forall t,
  epstep (phi_erase (instance_translate t)) (phi_erase t).
Proof.
  assert (Hb : forall bs,
    (forall c b, In (c,b) bs ->
      epstep (phi_erase (instance_translate c)) (phi_erase c) /\
      epstep (phi_erase (instance_translate b)) (phi_erase b)) ->
    epbranches
      (map (fun '(c,b) => (phi_erase (instance_translate c),
                          phi_erase (instance_translate b))) bs)
      (map (fun '(c,b) => (phi_erase c, phi_erase b)) bs)).
  { intros bs HH. induction bs as [|[c b] bs IH]; cbn; constructor.
    - exact (proj1 (HH c b (or_introl eq_refl))).
    - exact (proj2 (HH c b (or_introl eq_refl))).
    - apply IH. intros c' b' Hin. apply HH. right; exact Hin. }
  apply (tsize_strong_ind (fun t =>
    epstep (phi_erase (instance_translate t)) (phi_erase t))).
  intros t IH. destruct t; cbn;
    try solve [constructor];
    try solve [constructor; apply IH;
      try pose proof (tsize_pos t1); try pose proof (tsize_pos t2); cbn; lia].
  - change (epstep (TLam (TApp (lift 1 0 (TMuS TUnit)) (TVar 0)))
        (TMuS TUnit)).
    apply eps_eta, epstep_refl.
  - rewrite map_map. cbn.
    apply eps_case.
    + apply IH; cbn; lia.
    + apply IH; cbn; lia.
    + erewrite map_ext with
        (g := fun '(c,b) => (phi_erase (instance_translate c),
                            phi_erase (instance_translate b)));
        [|intros [c b]; reflexivity].
      apply Hb. intros c b Hin. split; apply IH;
        [eapply tsize_case_bs | eapply tsize_case_bs_body]; exact Hin.
Qed.
End SignatureInstances.

(* Checked signature-transport component: SignatureProgressReduction. *)
Module SignatureProgressReduction.
(* The remaining signature transport obligation suffices for progress.
   This theorem has an explicit premise; it does not discharge that obligation. *)
Import SignatureLemmas SignatureConversion.
Import ListNotations TypeRulesCore.

Definition signature_tag_transport : Prop :=
  forall N E0 S0 i0 E1 S1 i1 c n xs X bs,
    bounded_progress_parent N -> tsize xs <= N ->
    check [] xs (TInterp (TApp (branches (TApp S0 i0)) c) X) ->
    sub [] (TApp (SigMu E0 S0) i0) (TApp (SigMu E1 S1) i1) ->
    enum_pos c n -> Forall (fun d => exists m, enum_pos d m) bs ->
    spine_mem c (labels (TApp S0 i0)) ->
    covers bs (labels (TApp S1 i1)) ->
    (exists d, In d bs /\ enum_pos d n) \/ exists xs', step xs xs'.

Section TransportReduction.
Variable Htransport : signature_tag_transport.

Lemma progress_n_transport : forall N,
    (forall t A, tsize t <= N -> check [] t A ->
       value t \/ exists t', step t t') /\
    (forall c T, tsize c <= N -> check [] c T -> whd T HEnumT ->
       (exists m, enum_pos c m) \/ exists c', step c c').
Proof.
  induction N as [|N IH].
  { split.
    - intros t A Hsz _. pose proof (tsize_pos t). lia.
    - intros c T Hsz _ _. pose proof (tsize_pos c). lia. }
  destruct IH as [IHmain IHpos].
  assert (Hmain : forall t A, tsize t <= S N -> check [] t A ->
                    value t \/ exists t', step t t').
  { intros t A Hsz Hck.
    destruct t as [ n | k | A0 B0 | b | f a | A0 B0 | a b | p | p
                  | | | | s | | | tg E | E | | n' | E P
                  | E P p e | IT | i | | A0 B0 | Sd T | Sd T | E T
                  | D X | R | Sf | x | R P stp i x | D X xs P
                  | D X P h0 xs | A0 | A0 | A0 a l | M Q bs ];
      try (solve [left; constructor]).
    - (* TVar *)
      exfalso. exact (inv_var [] (TVar n) A Hck eq_refl n eq_refl).
    - (* TApp *)
      destruct (inv_app [] (TApp f a) A Hck eq_refl f a eq_refl)
        as [T' [Hf HwPi]].
      assert (Hszf : tsize f <= N) by (cbn in Hsz; lia).
      destruct (IHmain f T' Hszf Hf) as [Hv | [f' Hstep]];
        [| right; eexists; apply st_app1; exact Hstep].
      pose proof (canon_main [] f T' Hf eq_refl Hv T' HPi (cv_refl T') HwPi)
        as K. cbn in K.
      destruct K as [[b0 ->] | [[R0 ->] | [Sf0 ->]]].
      + right. eexists. apply st_beta.
      + left. constructor.
      + left. constructor.
    - (* TFst *)
      destruct (inv_fst [] (TFst p) A Hck eq_refl p eq_refl)
        as [T' [Hp HwS]].
      assert (Hszp : tsize p <= N) by (cbn in Hsz; lia).
      destruct (IHmain p T' Hszp Hp) as [Hv | [p' Hstep]];
        [| right; eexists; apply st_fst1; exact Hstep].
      pose proof (canon_main [] p T' Hp eq_refl Hv T' HSigma (cv_refl T') HwS)
        as K. cbn in K.
      destruct K as [a0 [b0 ->]].
      right. eexists. apply st_fst.
    - (* TSnd *)
      destruct (inv_snd [] (TSnd p) A Hck eq_refl p eq_refl)
        as [T' [Hp HwS]].
      assert (Hszp : tsize p <= N) by (cbn in Hsz; lia).
      destruct (IHmain p T' Hszp Hp) as [Hv | [p' Hstep]];
        [| right; eexists; apply st_snd1; exact Hstep].
      pose proof (canon_main [] p T' Hp eq_refl Hv T' HSigma (cv_refl T') HwS)
        as K. cbn in K.
      destruct K as [a0 [b0 ->]].
      right. eexists. apply st_snd.
    - (* TEPi *)
      pose proof (inv_epi [] (TEPi E P) A Hck eq_refl E P eq_refl) as HEnum.
      assert (HszE : tsize E <= N) by (cbn in Hsz; lia).
      destruct (IHmain E TEnumU HszE HEnum) as [Hv | [E' Hstep]];
        [| right; eexists; apply st_epi1; exact Hstep].
      pose proof (canon_main [] E TEnumU HEnum eq_refl Hv TEnumU HEnumU
                    (cv_refl TEnumU) (whd_shape TEnumU HEnumU hs_enumu))
        as K. cbn in K.
      destruct K as [-> | [tg0 [E0 ->]]].
      + right. eexists. apply st_epi_nil.
      + right. eexists. apply st_epi_cons.
    - (* TSwitch *)
      destruct (inv_switch [] (TSwitch E P p e) A Hck eq_refl E P p e eq_refl)
        as (HEnum & Hp & He).
      assert (HszE : tsize E <= N) by (cbn in Hsz; lia).
      destruct (IHmain E TEnumU HszE HEnum) as [HvE | [E' Hstep]];
        [| right; eexists; apply st_switch1; exact Hstep].
      pose proof (canon_main [] E TEnumU HEnum eq_refl HvE TEnumU HEnumU
                    (cv_refl TEnumU) (whd_shape TEnumU HEnumU hs_enumu))
        as KE. cbn in KE.
      destruct KE as [-> | [tg0 [E0 ->]]].
      + (* nil enum: the scrutinee cannot be a value *)
        assert (Hsze : tsize e <= N) by (cbn in Hsz; lia).
        destruct (IHmain e (TEnumT TNilE) Hsze He) as [Hve | [e' Hstep]];
          [| right; eexists; apply st_switch4; exact Hstep].
        exfalso.
        pose proof (canon_main [] e (TEnumT TNilE) He eq_refl Hve
                      (TEnumT TNilE) HEnumT (cv_refl _)
                      (whd_shape _ _ (hs_enumt TNilE))) as Ke.
        cbn in Ke. destruct Ke as (tg1 & E1 & Hcvt & _).
        exact (conv_enumt_cons_nil_absurd tg1 E1 Hcvt).
      + (* cons enum *)
        assert (Hszp : tsize p <= N) by (cbn in Hsz; lia).
        assert (HwS : whd (TEPi (TConsE tg0 E0) P) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_epi_cons | apply ev_refl].
          - constructor. }
        destruct (IHmain p (TEPi (TConsE tg0 E0) P) Hszp Hp)
          as [Hvp | [p' Hstep]];
          [| right; eexists; apply st_switch3; exact Hstep].
        pose proof (canon_main [] p _ Hp eq_refl Hvp _ HSigma (cv_refl _) HwS)
          as Kp. cbn in Kp.
        destruct Kp as [p0 [ps ->]].
        assert (Hsze : tsize e <= N) by (cbn in Hsz; lia).
        destruct (IHmain e (TEnumT (TConsE tg0 E0)) Hsze He)
          as [Hve | [e' Hstep]];
          [| right; eexists; apply st_switch4; exact Hstep].
        pose proof (canon_main [] e _ He eq_refl Hve _ HEnumT (cv_refl _)
                      (whd_shape _ _ (hs_enumt (TConsE tg0 E0)))) as Ke.
        cbn in Ke. destruct Ke as (tg1 & E1 & _ & [-> | [n0 [-> _]]]).
        * right. eexists. apply st_switch_zero.
        * right. eexists. apply st_switch_succ.
    - (* TInterp *)
      destruct (inv_interp [] (TInterp D X) A Hck eq_refl D X eq_refl)
        as [IT0 HD].
      assert (HszD : tsize D <= N) by (cbn in Hsz; lia).
      destruct (IHmain D (TIDesc IT0) HszD HD) as [HvD | [D' Hstep]];
        [| right; eexists; apply st_interp1; exact Hstep].
      pose proof (canon_main [] D _ HD eq_refl HvD _ HIDesc (cv_refl _)
                    (whd_shape _ _ (hs_idesc IT0))) as K. cbn in K.
      destruct K as [K1 | [K2 | [K3 | [K4 | [K5 | K6]]]]].
      + destruct K1 as [i0 K1]. subst D. right. eexists. apply st_interp_var.
      + subst D. right. eexists. apply st_interp_one.
      + destruct K3 as [A1 [B1 K3]]. subst D.
        right. eexists. apply st_interp_prod.
      + destruct K4 as [S1 [T1 K4]]. subst D.
        right. eexists. apply st_interp_pi.
      + destruct K5 as [S1 [T1 K5]]. subst D.
        right. eexists. apply st_interp_sig.
      + destruct K6 as [E1 [T1 K6]]. subst D.
        right. eexists. apply st_interp_choice.
    - (* TInd *)
      pose proof (inv_ind [] (TInd R P stp i x) A Hck eq_refl
                    R P stp i x eq_refl) as Hx.
      assert (Hszx : tsize x <= N) by (cbn in Hsz; lia).
      destruct (IHmain x _ Hszx Hx) as [Hvx | [x' Hstep]];
        [| right; eexists; apply st_ind5; exact Hstep].
      pose proof (canon_main [] x _ Hx eq_refl Hvx _ HMuIApp (cv_refl _)
                    (whd_shape _ _ (hs_muiapp R i))) as K. cbn in K.
      destruct K as [xs0 ->].
      right. eexists. apply st_ind.
    - (* TIAll *)
      destruct (inv_iall [] (TIAll D X xs P) A Hck eq_refl D X xs P eq_refl)
        as [[IT0 HD] Hxs].
      assert (HszD : tsize D <= N) by (cbn in Hsz; lia).
      destruct (IHmain D (TIDesc IT0) HszD HD) as [HvD | [D' Hstep]];
        [| right; eexists; apply st_iall1; exact Hstep].
      pose proof (canon_main [] D _ HD eq_refl HvD _ HIDesc (cv_refl _)
                    (whd_shape _ _ (hs_idesc IT0))) as K. cbn in K.
      assert (Hszxs : tsize xs <= N) by (cbn in Hsz; lia).
      destruct K as [K1 | [K2 | [K3 | [K4 | [K5 | K6]]]]].
      + destruct K1 as [i0 K1]. subst D. right. eexists. apply st_iall_var.
      + subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_iall3; exact Hstep].
        assert (Hw1 : whd (TInterp TI1 X) HUnitT).
        { eexists. split.
          - eapply ev_step; [apply st_interp_one | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HUnitT (cv_refl _)
                      Hw1) as Kx. cbn in Kx. subst xs.
        right. eexists. apply st_iall_one.
      + destruct K3 as [A1 [B1 K3]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_iall3; exact Hstep].
        assert (Hw1 : whd (TInterp (TIProd A1 B1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_prod | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_iall_prod.
      + destruct K4 as [S1 [T1 K4]]. subst D. right. eexists. apply st_iall_pi.
      + destruct K5 as [S1 [T1 K5]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_iall3; exact Hstep].
        assert (Hw1 : whd (TInterp (TISig S1 T1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_sig | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_iall_sig.
      + destruct K6 as [E1 [T1 K6]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_iall3; exact Hstep].
        assert (Hw1 : whd (TInterp (TIChoice E1 T1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_choice | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_iall_choice.
    - (* THyps *)
      destruct (inv_hyps [] (THyps D X P h0 xs) A Hck eq_refl
                  D X P h0 xs eq_refl)
        as [[IT0 HD] Hxs].
      assert (HszD : tsize D <= N) by (cbn in Hsz; lia).
      destruct (IHmain D (TIDesc IT0) HszD HD) as [HvD | [D' Hstep]];
        [| right; eexists; apply st_hyps1; exact Hstep].
      pose proof (canon_main [] D _ HD eq_refl HvD _ HIDesc (cv_refl _)
                    (whd_shape _ _ (hs_idesc IT0))) as K. cbn in K.
      assert (Hszxs : tsize xs <= N) by (cbn in Hsz; lia).
      destruct K as [K1 | [K2 | [K3 | [K4 | [K5 | K6]]]]].
      + destruct K1 as [i0 K1]. subst D. right. eexists. apply st_hyps_var.
      + subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_hyps5; exact Hstep].
        assert (Hw1 : whd (TInterp TI1 X) HUnitT).
        { eexists. split.
          - eapply ev_step; [apply st_interp_one | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HUnitT (cv_refl _)
                      Hw1) as Kx. cbn in Kx. subst xs.
        right. eexists. apply st_hyps_one.
      + destruct K3 as [A1 [B1 K3]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_hyps5; exact Hstep].
        assert (Hw1 : whd (TInterp (TIProd A1 B1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_prod | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_hyps_prod.
      + destruct K4 as [S1 [T1 K4]]. subst D. right. eexists. apply st_hyps_pi.
      + destruct K5 as [S1 [T1 K5]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_hyps5; exact Hstep].
        assert (Hw1 : whd (TInterp (TISig S1 T1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_sig | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_hyps_sig.
      + destruct K6 as [E1 [T1 K6]]. subst D.
        destruct (IHmain xs _ Hszxs Hxs) as [Hvxs | [xs' Hstep]];
          [| right; eexists; apply st_hyps5; exact Hstep].
        assert (Hw1 : whd (TInterp (TIChoice E1 T1) X) HSigma).
        { eexists. split.
          - eapply ev_step; [apply st_interp_choice | apply ev_refl].
          - constructor. }
        pose proof (canon_main [] xs _ Hxs eq_refl Hvxs _ HSigma (cv_refl _)
                      Hw1) as Kx. cbn in Kx.
        destruct Kx as [a0 [b0 Kx]]. subst xs.
        right. eexists. apply st_hyps_choice.
    - (* TCase *)
      destruct (inv_case [] (TCase M Q bs) A Hck eq_refl M Q bs eq_refl)
        as (Sf & i & IT & E & Phi & HM & HIT & HE & HSf & Hi & Hlab & Hcov & Hcb).
      assert (HszM : tsize M <= N) by (cbn in Hsz; lia).
      destruct (IHmain M _ HszM HM) as [HvM | [M' HstM]];
        [| right; eexists; apply st_case1; exact HstM].
      pose proof (canon_main [] M _ HM eq_refl HvM _ HMuSApp (cv_refl _)
                    (whd_shape _ _ (hs_musapp (TPair E Sf) i))) as K.
      cbn in K. destruct K as (c & xs & E0 & -> & Hc0).
      assert (Hszc : tsize c <= N) by (cbn in Hsz; lia).
      destruct (IHpos c _ Hszc Hc0 (whd_shape _ _ (hs_enumt E0)))
        as [[n Hn] | [c' Hstc]];
        [| right; eexists; apply st_case1; apply st_in1; apply st_pair1;
           exact Hstc].
      pose proof (cb_labels [] Sf i E Q bs Hcb) as HFlab.
      assert (HFps : Forall (fun cb => (exists m, enum_pos (fst cb) m) \/
                                       (exists c'0, step (fst cb) c'0)) bs).
      { rewrite Forall_forall in HFlab. apply Forall_forall.
        intros [cj bj] Hin.
        assert (Hszj : tsize cj <= N).
        { pose proof (tsize_case_bs (TIn (TPair c xs)) Q bs cj bj Hin). lia. }
        specialize (HFlab _ Hin). cbn in HFlab.
        exact (IHpos cj _ Hszj HFlab (whd_shape _ _ (hs_enumt E))). }
      destruct (labels_walk bs HFps)
        as [[bs1 [c0 [b0 [bs2 [c0' [-> Hst0]]]]]] | Hall];
        [right; eexists; eapply st_case_lbl; exact Hst0 |].
      destruct (forall_ex_forall2 bs Hall) as [ns Hns].
      destruct (in_pair_mus_origin c xs E Sf i HM)
        as (S0 & i0 & IT0 & Eorig & Phi0 & HIT0 & HE0 & HS0 & Hi0 &
            Hc_orig & HL0 & Hmem0 & Hxs0 & Hconv0).
      assert (Hszxs : tsize xs <= N) by (cbn in Hsz; lia).
      assert (HmemL0 : spine_mem c (labels (TApp S0 i0))).
      { eapply spine_mem_pre; eassumption. }
      assert (HcovL : covers (map fst bs) (labels (TApp Sf i))).
      { eapply covers_pre; [exact Hlab | exact Hcov]. }
      assert (Hallmap : Forall (fun d => exists m, enum_pos d m) (map fst bs)).
      { rewrite Forall_forall in Hall |- *.
        intros d Hd. apply in_map_iff in Hd.
        destruct Hd as [[dc db] [Heq Hin]]. subst d. exact (Hall _ Hin). }
      destruct (Htransport N Eorig S0 i0 E Sf i c n xs (Carrier Eorig S0)
          (map fst bs) IHmain Hszxs Hxs0 Hconv0 Hn Hallmap HmemL0 HcovL)
        as [[d [Hind Hdn]] | [xsnext Hstepxs]].
      2: { right. eexists. apply st_case1, st_in1, st_pair2. exact Hstepxs. }
      apply in_map_iff in Hind. destruct Hind as [[d0 bd] [Hfst Hinbs]].
      cbn in Hfst. subst d0.
      destruct (forall2_in_l _ _ _ _ _ _ Hns Hinbs) as [m [Hinm Hpm]].
      cbn in Hpm.
      assert (Hmn : n = m) by (eapply enum_pos_functional; eassumption).
      subst m.
      destruct (find_first bs ns n Hns Hinm) as (k & ck & bk & Hnth & Hpk & Hpre).
      right. eexists.
      eapply st_case with (k := k) (n := n);
        [exact Hnth | exact Hpk | exact Hn | exact Hpre]. }
  split; [exact Hmain |].
  intros c T Hsz Hck HwT.
  destruct (Hmain c T Hsz Hck) as [Hv | Hs]; [| right; exact Hs].
  destruct HwT as [T' [HevT HshT]].
  pose proof (canon_main [] c T Hck eq_refl Hv T HEnumT (cv_refl T)
                (ex_intro _ T' (conj HevT HshT))) as K.
  cbn in K. destruct K as (tg1 & E1 & _ & [-> | [n' [-> [E2 Hn']]]]).
  - left. exists 0. constructor.
  - assert (Hszn : tsize n' <= N) by (cbn in Hsz; lia).
    destruct (IHpos n' _ Hszn Hn' (whd_shape _ _ (hs_enumt E2)))
      as [[m Hm] | [n'' Hstn]].
    + left. exists (S m). constructor. exact Hm.
    + right. eexists. apply st_esucc1. exact Hstn.
Qed.

Theorem progress_from_signature_tag_transport : forall t A,
    check [] t A -> value t \/ exists t', step t t'.
Proof.
  intros t A Hck.
  destruct (progress_n_transport (tsize t)) as [Hmain _].
  exact (Hmain t A (le_n (tsize t)) Hck).
Qed.
End TransportReduction.
End SignatureProgressReduction.

(* Checked signature-transport component: _parent_instance_pruning. *)
Module _parent_instance_pruning.
(* Directed pruning of explicit signature instances. *)
Import SignatureConversion SignatureInstances ErasureCounterexample.
Import ListNotations TypeRulesCore _tmp_epstep
 _tmp_epstep_subst _tmp_commute
 _work_mixed_closure _work_cjoin
 _work_cstep_invariants _work_conv_whd_pos
 _luna_phi_erase_shapes MuApplicationSort.

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
End _parent_instance_pruning.

(* Checked signature-transport component: _luna_instance_membership. *)
Module _luna_instance_membership.
Import SignatureConversion _parent_instance_pruning.
Import ListNotations TypeRulesCore.
Import _work_cjoin _work_cstep_invariants.

Inductive joined_mem (c : term) : term -> Prop :=
| jm_here : forall L A d R,
    cjoin L (TLCons A d R) -> cjoin c d -> joined_mem c L
| jm_there : forall L A d R,
    cjoin L (TLCons A d R) -> joined_mem c R -> joined_mem c L.

Lemma joined_mem_transport : forall c L1,
  joined_mem c L1 -> forall L2, cjoin L1 L2 -> joined_mem c L2.
Proof.
  intros c L1 H. induction H as [L A d R HL Hc | L A d R HL Htail IH]; intros L2 H12.
  - apply jm_here with (L := L2) (A := A) (d := d) (R := R).
    + eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL].
    + exact Hc.
  - apply jm_there with (L := L2) (A := A) (d := d) (R := R).
    + eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL].
    + assert (HC : cjoin L2 (TLCons A d R)).
      { eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL]. }
      exact Htail.
Qed.

Lemma joined_mem_cons_inv : forall c A d R,
  joined_mem c (TLCons A d R) ->
  cjoin c d \/ joined_mem c R.
Proof.
  intros c A d R H. inversion H; subst.
  - left.
    destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ H0) as [_ [Hcd _]].
    eapply cjoin_trans; [exact H1|apply cjoin_sym; exact Hcd].
  - right.
    destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ H0) as [_ [_ Hlr]].
    eapply joined_mem_transport; [exact H1|apply cjoin_sym; exact Hlr].
Qed.

Lemma prune_labels_joined_mem : forall B L L',
  prune_labels B L L' -> forall c P,
  joined_mem (phi_erase c) (phi_erase L) ->
  (forall d, cjoin (phi_erase c) (phi_erase d) ->
    instance_dead (TApp B d) -> P) ->
  joined_mem (phi_erase c) (phi_erase L') \/ P.
Proof.
  intros B L L' H. induction H; intros x P Hmem HP.
  - left. eapply joined_mem_transport; [exact Hmem|].
    assert (Heq : phi_erase L = phi_erase L') by
      (apply prune_erase; assumption).
    rewrite Heq. apply cjoin_refl.
  - destruct (joined_mem_cons_inv _ _ _ _ Hmem) as [Hhead|Htail].
    + change (cjoin (phi_erase x) (phi_erase c)) in Hhead.
      rewrite (prune_erase _ _ H0) in Hhead.
      left. apply jm_here with (L := phi_erase (TLCons A' c' L'))
        (A := phi_erase A') (d := phi_erase c') (R := phi_erase L').
      * apply cjoin_refl.
      * eapply cjoin_trans; [exact Hhead|].
        apply cjoin_refl.
    + destruct (IHprune_labels x P Htail HP) as [Ht|Hp].
      * left. eapply jm_there; [apply cjoin_refl|exact Ht].
      * right; exact Hp.
  - destruct (joined_mem_cons_inv _ _ _ _ Hmem) as [Hhead|Htail].
    + right. eapply HP; [exact Hhead|].
      assumption.
    + destruct (IHprune_labels x P Htail HP) as [Ht|Hp].
      * left; exact Ht.
      * right; exact Hp.
Qed.
End _luna_instance_membership.

(* Checked signature-transport component: _luna_instance_coverage. *)
Module _luna_instance_coverage.
Import SignatureConversion _parent_instance_pruning _luna_instance_membership.
Import ListNotations TypeRulesCore.
Import _work_cjoin _work_cstep_invariants.

Inductive joined_covers (bs : list term) : term -> Prop :=
| jc_nil : forall L A, cjoin L (TLNil A) -> joined_covers bs L
| jc_cons : forall L A d R,
    cjoin L (TLCons A d R) ->
    (exists b, In b bs /\ cjoin (phi_erase b) d) ->
    joined_covers bs R -> joined_covers bs L.

Lemma joined_covers_transport : forall bs L1,
  joined_covers bs L1 -> forall L2, cjoin L1 L2 -> joined_covers bs L2.
Proof.
 intros bs L1 H; induction H as [L A HL|L A d R HL Hb Htail IH]; intros L2 H12.
 - apply jc_nil with (A:=A). eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL].
 - apply jc_cons with (A:=A) (d:=d) (R:=R).
   + eapply cjoin_trans; [apply cjoin_sym; exact H12|exact HL].
   + exact Hb.
   + exact Htail.
Qed.

Lemma joined_covers_cons_inv : forall bs A d R,
  joined_covers bs (TLCons A d R) ->
  (exists b, In b bs /\ cjoin (phi_erase b) d) /\ joined_covers bs R.
Proof.
 intros bs A d R H.
 inversion H as [L0 A0 Hnil | L0 A0 d0 R0 Hlist Hhead Htail].
 - exfalso. eapply no_cjoin_lcons_lnil_luna; eassumption.
 - destruct (cjoin_lcons_inv_erased_luna _ _ _ _ _ _ Hlist)
     as [_ [Hdd0 HRR0]].
   split.
   + destruct Hhead as [b [Hb Hbd0]]. exists b; split; [exact Hb|].
     eapply cjoin_trans; [exact Hbd0|apply cjoin_sym; exact Hdd0].
   + eapply joined_covers_transport; [exact Htail|apply cjoin_sym; exact HRR0].
Qed.

Lemma prune_labels_joined_covers : forall B L L' bs,
  prune_labels B L L' -> joined_covers bs (phi_erase L) ->
  joined_covers bs (phi_erase L').
Proof.
 intros B L L' bs H; induction H as
   [B0 L0 L'0 Hpr
   |B0 A A' c c' L0 L'0 HA Hc Hpl IH
   |B0 A c L0 L'0 Hdead Hpl IH]; intros HC.
 - rewrite <- (prune_erase _ _ Hpr). exact HC.
 - destruct (joined_covers_cons_inv _ _ _ _ HC) as [Hhead Htail].
   apply jc_cons with (A:=phi_erase A') (d:=phi_erase c') (R:=phi_erase L'0).
   + apply cjoin_refl.
   + rewrite <- (prune_erase _ _ Hc). exact Hhead.
   + exact (IH Htail).
 - destruct (joined_covers_cons_inv _ _ _ _ HC) as [_ Htail].
   exact (IH Htail).
Qed.

Lemma covers_joined : forall bs L, covers bs L -> joined_covers bs (phi_erase L).
Proof.
 intros bs L H; induction H.
 - apply jc_nil with (A:=phi_erase A).
   pose proof (conv_of_eval Phi (TLNil A) H) as HC.
   exact (conv_phi_cjoin _ _ HC).
 - apply jc_cons with (A:=phi_erase A) (d:=phi_erase c) (R:=phi_erase Phi').
   + pose proof (conv_of_eval Phi (TLCons A c Phi') H) as HC.
     exact (conv_phi_cjoin _ _ HC).
   + apply Exists_exists in H0. destruct H0 as [b [Hb Hbc]]. exists b; split; [exact Hb|].
     eapply cjoin_trans; [apply cjoin_sym; apply conv_phi_cjoin; exact Hbc|apply cjoin_refl].
   + exact IHcovers.
Qed.


Lemma joined_mem_nil_absurd : forall c A,
  joined_mem c (TLNil A) -> False.
Proof.
 intros c A H.
 inversion H as [L A0 d R HL Hc | L A0 d R HL Htail].
 - apply (no_cjoin_lcons_lnil_luna A0 d R A). apply cjoin_sym. exact HL.
 - apply (no_cjoin_lcons_lnil_luna A0 d R A). apply cjoin_sym. exact HL.
Qed.

Lemma joined_mem_covered : forall c L bs,
  joined_mem c L -> joined_covers bs L ->
  exists d, In d bs /\ cjoin c (phi_erase d).
Proof.
 intros c L bs Hm Hcov. revert Hm.
 induction Hcov as [L A HL | L A d R HL [b [Hb Hbd]] Htail IH]; intro Hm.
 - exfalso.
   apply joined_mem_nil_absurd with (c:=c) (A:=A).
   eapply joined_mem_transport; [exact Hm|exact HL].
 - pose proof (joined_mem_transport c L Hm (TLCons A d R) HL) as Hmx.
   destruct (joined_mem_cons_inv c A d R Hmx) as [Hcd|Hmt].
   + exists b. split; [exact Hb|].
     eapply cjoin_trans; [exact Hcd|apply cjoin_sym; exact Hbd].
   + exact (IH Hmt).
Qed.
End _luna_instance_coverage.

(* Checked signature-transport component: _luna_instance_phi_spine. *)
Module _luna_instance_phi_spine.
Import SignatureInstances SignatureConversion _parent_instance_pruning.
Import ListNotations TypeRulesCore.
Import _tmp_epstep _work_mixed_closure
  _work_cjoin _work_cstep_invariants.

Lemma instance_translate_eval_luna : forall t u, eval t u ->
  eval (instance_translate t) (instance_translate u).
Proof.
  intros t u H; induction H as [t|t v u Hstep Heval IH].
  - apply ev_refl.
  - eapply ev_step; [apply instance_translate_step; exact Hstep|exact IH].
Qed.

Lemma instance_translate_eval_fconv_luna : forall t u, eval t u ->
  fconv (instance_translate t) (instance_translate u).
Proof.
  intros t u H; induction H as [t|t v u Hstep Heval IH].
  - apply fc_refl.
  - eapply fc_trans; [apply instance_translate_fstep; apply fs_step; exact Hstep|exact IH].
Qed.

Lemma fconv_lcons_tail_luna : forall A c L L',
  fconv L L' -> fconv (TLCons A c L) (TLCons A c L').
Proof.
  intros A c L L' H.
  apply (fconv_map (fun z => TLCons A c z)).
  intros x y Hxy. apply fs_lcons3. exact Hxy.
  exact H.
Qed.

Lemma instance_dead_translate_luna : forall D,
  desc_against D -> instance_dead (instance_translate D).
Proof.
  intros D HD. exists D. split; [exact HD|].
  exists (phi_erase D). split.
  - apply rtc_one. apply epstep_cstep. apply instance_translate_erased_eta.
  - apply rtc_refl.
Qed.

Lemma instance_phi_spine_aux : forall Sf i Phi Psi,
  spine_phi Sf i Phi Psi ->
  exists L0,
    fconv (instance_translate Phi) L0  /\
    prune_labels
      (branches (TApp (instance_translate Sf) (instance_translate i)))
      L0 (instance_translate Psi).
Proof.
  intros Sf i Phi Psi H; induction H.
  - exists (instance_translate (TLNil A)). split.
    + apply instance_translate_eval_fconv_luna. exact H.
    + apply pl_stop. apply prune_term_refl.
  - destruct IHspine_phi as [L0 [Hf Hp]].
    exists (TLCons (instance_translate A) (instance_translate c) L0).
    split.
    + eapply fc_trans.
      * apply instance_translate_eval_fconv_luna. exact H.
      * apply fconv_lcons_tail_luna. exact Hf.
    + apply pl_keep; try apply prune_term_refl. exact Hp.
  - destruct IHspine_phi as [L0 [Hf Hp]].
    exists (TLCons (instance_translate A) (instance_translate c) L0). split.
    + eapply fc_trans.
      * apply instance_translate_eval_fconv_luna. exact H.
      * apply fconv_lcons_tail_luna. exact Hf.
    + apply pl_drop.
      * change (instance_dead (instance_translate (TApp (branches (TApp Sf i)) c))).
        apply instance_dead_translate_luna. exact H0.
      * exact Hp.
  - exists (instance_translate Phi). split.
    + apply fc_refl.
    + apply pl_stop. apply prune_term_refl.
Qed.

Theorem instance_phi_spine_luna : forall Sf i Phi Psi,
  spine_phi Sf i Phi Psi ->
  exists L0, fconv (instance_translate Phi) L0  /\
    prune_labels (branches (TApp (instance_translate Sf) (instance_translate i)))
      L0 (instance_translate Psi).
Proof. exact instance_phi_spine_aux. Qed.
End _luna_instance_phi_spine.

(* Checked signature-transport component: _luna_instance_conversion. *)
Module _luna_instance_conversion.
Import SignatureInstances SignatureConversion ErasureCounterexample _parent_instance_pruning _luna_instance_phi_spine.
Import ListNotations TypeRulesCore.
Import _tmp_epstep _work_mixed_closure
  _work_cjoin _work_cstep_invariants.

Inductive instance_conv : term -> term -> Prop :=
| ic_core : forall t u, fconv t u -> instance_conv t u
| ic_prune : forall t u, prune_term t u -> instance_conv t u
| ic_refl : forall t, instance_conv t t
| ic_sym : forall t u, instance_conv t u -> instance_conv u t
| ic_trans : forall t u v, instance_conv t u -> instance_conv u v -> instance_conv t v.

Lemma ic_map : forall (F : term -> term),
  (forall x y, fstep x y -> fstep (F x) (F y)) ->
  (forall x y, prune_term x y -> prune_term (F x) (F y)) ->
  forall x y, instance_conv x y -> instance_conv (F x) (F y).
Proof.
  intros F HF HP x y H; induction H.
  - apply ic_core. eapply fconv_map; [exact HF | exact H].
  - apply ic_prune. eauto.
  - apply ic_refl.
  - apply ic_sym. exact IHinstance_conv.
  - eapply ic_trans; eauto.
Qed.

Lemma ic_map2 : forall (F : term -> term -> term),
  (forall x y z, fstep x y -> fstep (F x z) (F y z)) ->
  (forall z x y, fstep x y -> fstep (F z x) (F z y)) ->
  (forall x y z, prune_term x y -> prune_term (F x z) (F y z)) ->
  (forall z x y, prune_term x y -> prune_term (F z x) (F z y)) ->
  forall x x' y y', instance_conv x x' -> instance_conv y y' ->
    instance_conv (F x y) (F x' y').
Proof.
  intros F Hf1 Hf2 Hp1 Hp2 x x' y y' Hx Hy.
  eapply ic_trans.
  - eapply (ic_map (fun z => F z y)
        (fun a b H => Hf1 a b y H)
        (fun a b H => Hp1 a b y H)); exact Hx.
  - eapply (ic_map (fun z => F x' z)
        (fun a b H => Hf2 x' a b H)
        (fun a b H => Hp2 x' a b H)); exact Hy.
Qed.

Lemma ic_lift : forall t u, instance_conv t u -> forall d k,
  instance_conv (lift d k t) (lift d k u).
Proof.
  intros t u H; induction H; intros d k.
  - apply ic_core. apply fconv_lift_parent. exact H.
  - apply ic_prune. apply prune_lift. exact H.
  - apply ic_refl.
  - apply ic_sym. exact (IHinstance_conv d k).
  - eapply ic_trans; [exact (IHinstance_conv1 d k)|exact (IHinstance_conv2 d k)].
Qed.

Lemma ic_signature_prune : forall Sf i Phi Psi,
  eval (labels (TApp Sf i)) Phi ->
  spine_phi Sf i Phi Psi ->
  instance_conv (instance_translate (TApp (TMuS Sf) i))
    (signature_instance
      (branches (TApp (instance_translate Sf) (instance_translate i)))
      (instance_translate Psi) (instance_translate i)).
Proof.
  intros Sf i Phi Psi Heval Hsp.
  destruct (instance_phi_spine_luna Sf i Phi Psi Hsp)
    as [L0 [Hf Hpl]].
  pose proof (instance_translate_musapp Sf i) as Hstep.
  assert (Hbase : instance_conv
      (instance_translate (TApp (TMuS Sf) i))
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        (labels (TApp (instance_translate Sf) (instance_translate i)))
        (instance_translate i))).
  { apply ic_core. apply fc_step. apply fs_step. exact Hstep. }
  assert (Htranslated : fconv
      (labels (TApp (instance_translate Sf) (instance_translate i)))
      (instance_translate Phi)).
  { pose proof (instance_translate_eval_fconv_luna _ _ Heval) as Htmp.
    cbn [instance_translate] in Htmp. exact Htmp. }
  assert (Hlabels : instance_conv
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        (labels (TApp (instance_translate Sf) (instance_translate i)))
        (instance_translate i))
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        L0 (instance_translate i))).
  { apply (ic_map
      (fun z => signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        z (instance_translate i))).
    - intros x y Hxy. apply fs_app1. apply fs_mus. apply fs_pair2. exact Hxy.
    - intros x y Hxy. apply pt_app.
      + apply pt_mus. apply pt_pair; [apply prune_term_refl | exact Hxy].
      + exact (prune_term_refl _).
    - eapply ic_trans.
      + apply ic_core. exact Htranslated.
      + apply ic_core. exact Hf. }
  assert (Hprune : instance_conv
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        L0 (instance_translate i))
      (signature_instance
        (branches (TApp (instance_translate Sf) (instance_translate i)))
        (instance_translate Psi) (instance_translate i))).
  { apply ic_prune. apply pt_app.
    - apply pt_instance; [apply prune_term_refl | exact Hpl].
    - apply prune_term_refl. }
  eapply ic_trans; [exact Hbase|].
  eapply ic_trans; [exact Hlabels|exact Hprune].
Qed.

Lemma instance_branch_beta : forall S i,
  fconv
    (TApp (instance_translate
      (TLam (branches (TApp (lift 1 0 S) (TVar 0)))))
      (instance_translate i))
    (branches (TApp (instance_translate S) (instance_translate i))).
Proof.
  intros S i.
  cbn [instance_translate branches].
  rewrite instance_translate_lift.
  pose proof (st_beta
    (TFst (TApp (lift 1 0 (instance_translate S)) (TVar 0)))
    (instance_translate i)) as H.
  cbn [subst] in H.
  rewrite subst_lift_zero in H.
  rewrite _tmp_commute.lift_zero_id_local in H.
  apply fc_step. apply fs_step. exact H.
Qed.

Lemma ic_phi : forall S1 S2 i Phi1 Phi2 Psi1 Psi2,
  instance_conv
    (instance_translate (TLam (branches (TApp (lift 1 0 S1) (TVar 0)))))
    (instance_translate (TLam (branches (TApp (lift 1 0 S2) (TVar 0))))) ->
  eval (labels (TApp S1 i)) Phi1 ->
  eval (labels (TApp S2 i)) Phi2 ->
  spine_phi S1 i Phi1 Psi1 ->
  spine_phi S2 i Phi2 Psi2 ->
  instance_conv (instance_translate Psi1) (instance_translate Psi2) ->
  instance_conv (instance_translate (TApp (TMuS S1) i))
    (instance_translate (TApp (TMuS S2) i)).
Proof.
  intros S1 S2 i Phi1 Phi2 Psi1 Psi2 Hbranch He1 He2 Hp1 Hp2 Hpsi.
  pose proof (ic_signature_prune S1 i Phi1 Psi1 He1 Hp1) as Hleft.
  pose proof (ic_signature_prune S2 i Phi2 Psi2 He2 Hp2) as Hright.
  assert (HB : instance_conv
      (branches (TApp (instance_translate S1) (instance_translate i)))
      (branches (TApp (instance_translate S2) (instance_translate i)))).
  { eapply ic_trans.
    - apply ic_sym. apply ic_core. apply instance_branch_beta.
    - eapply ic_trans.
      + apply (ic_map (fun z => TApp z (instance_translate i))).
        * intros x y Hxy. apply fs_app1. exact Hxy.
        * intros x y Hxy. apply pt_app; [exact Hxy|apply prune_term_refl].
        * exact Hbranch.
      + apply ic_core. apply instance_branch_beta. }
  assert (Hmid : instance_conv
      (signature_instance
        (branches (TApp (instance_translate S1) (instance_translate i)))
        (instance_translate Psi1) (instance_translate i))
      (signature_instance
        (branches (TApp (instance_translate S2) (instance_translate i)))
        (instance_translate Psi2) (instance_translate i))).
  { apply (ic_map2 (fun B L => signature_instance B L (instance_translate i))).
    - intros x y z Hxy. apply fs_app1. apply fs_mus. apply fs_pair1. exact Hxy.
    - intros z x y Hxy. apply fs_app1. apply fs_mus. apply fs_pair2. exact Hxy.
    - intros x y z Hxy. apply pt_app.
      + apply pt_mus. apply pt_pair.
        * exact Hxy.
        * exact (prune_term_refl _).
      + exact (prune_term_refl _).
    - intros z x y Hxy. apply pt_app.
      + apply pt_mus. apply pt_pair.
        * exact (prune_term_refl _).
        * exact Hxy.
      + exact (prune_term_refl _).
    - exact HB.
    - exact Hpsi. }
  eapply ic_trans; [exact Hleft|].
  eapply ic_trans; [exact Hmid|].
  apply ic_sym. exact Hright.
Qed.

Lemma ic_map3 : forall (F : term -> term -> term -> term),
 (forall x y z q, fstep x y -> fstep (F x z q) (F y z q)) ->
 (forall z x y q, fstep x y -> fstep (F z x q) (F z y q)) ->
 (forall z q x y, fstep x y -> fstep (F z q x) (F z q y)) ->
 (forall x y z q, prune_term x y -> prune_term (F x z q) (F y z q)) ->
 (forall z x y q, prune_term x y -> prune_term (F z x q) (F z y q)) ->
 (forall z q x y, prune_term x y -> prune_term (F z q x) (F z q y)) ->
 forall x x' y y' z z', instance_conv x x' -> instance_conv y y' -> instance_conv z z' ->
 instance_conv (F x y z) (F x' y' z').
Proof.
 intros F H1 H2 H3 P1 P2 P3 x x' y y' z z' Hx Hy Hz.
 eapply ic_trans.
 - eapply (ic_map (fun a => F a y z)); [intros; eapply H1; eauto|intros; eapply P1; eauto|exact Hx].
 - eapply ic_trans.
   + eapply (ic_map (fun b => F x' b z)); [intros; eapply H2; eauto|intros; eapply P2; eauto|exact Hy].
   + eapply (ic_map (fun c => F x' y' c)); [intros; eapply H3; eauto|intros; eapply P3; eauto|exact Hz].
Qed.

Lemma ic_map4 : forall (F : term -> term -> term -> term -> term),
 (forall x y a b q, fstep x y -> fstep (F x a b q) (F y a b q)) ->
 (forall a x y b q, fstep x y -> fstep (F a x b q) (F a y b q)) ->
 (forall a b x y q, fstep x y -> fstep (F a b x q) (F a b y q)) ->
 (forall a b q x y, fstep x y -> fstep (F a b q x) (F a b q y)) ->
 (forall x y a b q, prune_term x y -> prune_term (F x a b q) (F y a b q)) ->
 (forall a x y b q, prune_term x y -> prune_term (F a x b q) (F a y b q)) ->
 (forall a b x y q, prune_term x y -> prune_term (F a b x q) (F a b y q)) ->
 (forall a b q x y, prune_term x y -> prune_term (F a b q x) (F a b q y)) ->
 forall a a' b b' c c' d d', instance_conv a a' -> instance_conv b b' -> instance_conv c c' -> instance_conv d d' ->
 instance_conv (F a b c d) (F a' b' c' d').
Proof.
 intros F H1 H2 H3 H4 P1 P2 P3 P4 a a' b b' c c' d d' Ha Hb Hc Hd.
 eapply ic_trans.
 - eapply (ic_map (fun x => F x b c d)); [intros; eapply H1; eauto|intros; eapply P1; eauto|exact Ha].
 - eapply ic_trans.
   + eapply (ic_map (fun x => F a' x c d)); [intros; eapply H2; eauto|intros; eapply P2; eauto|exact Hb].
   + eapply ic_trans.
     * eapply (ic_map (fun x => F a' b' x d)); [intros; eapply H3; eauto|intros; eapply P3; eauto|exact Hc].
     * eapply (ic_map (fun x => F a' b' c' x)); [intros; eapply H4; eauto|intros; eapply P4; eauto|exact Hd].
Qed.

Lemma ic_map5 : forall (F : term -> term -> term -> term -> term -> term),
 (forall x y a b c q, fstep x y -> fstep (F x a b c q) (F y a b c q)) ->
 (forall a x y b c q, fstep x y -> fstep (F a x b c q) (F a y b c q)) ->
 (forall a b x y c q, fstep x y -> fstep (F a b x c q) (F a b y c q)) ->
 (forall a b c x y q, fstep x y -> fstep (F a b c x q) (F a b c y q)) ->
 (forall a b c q x y, fstep x y -> fstep (F a b c q x) (F a b c q y)) ->
 (forall x y a b c q, prune_term x y -> prune_term (F x a b c q) (F y a b c q)) ->
 (forall a x y b c q, prune_term x y -> prune_term (F a x b c q) (F a y b c q)) ->
 (forall a b x y c q, prune_term x y -> prune_term (F a b x c q) (F a b y c q)) ->
 (forall a b c x y q, prune_term x y -> prune_term (F a b c x q) (F a b c y q)) ->
 (forall a b c q x y, prune_term x y -> prune_term (F a b c q x) (F a b c q y)) ->
 forall a a' b b' c c' d d' e e', instance_conv a a' -> instance_conv b b' -> instance_conv c c' -> instance_conv d d' -> instance_conv e e' ->
 instance_conv (F a b c d e) (F a' b' c' d' e').
Proof.
 intros F H1 H2 H3 H4 H5 P1 P2 P3 P4 P5 a a' b b' c c' d d' e e' Ha Hb Hc Hd He.
 eapply ic_trans.
 - eapply (ic_map (fun x => F x b c d e)); [intros; eapply H1; eauto|intros; eapply P1; eauto|exact Ha].
 - eapply ic_trans.
   + eapply (ic_map (fun x => F a' x c d e)); [intros; eapply H2; eauto|intros; eapply P2; eauto|exact Hb].
   + eapply ic_trans.
     * eapply (ic_map (fun x => F a' b' x d e)); [intros; eapply H3; eauto|intros; eapply P3; eauto|exact Hc].
     * eapply ic_trans.
       -- eapply (ic_map (fun x => F a' b' c' x e)); [intros; eapply H4; eauto|intros; eapply P4; eauto|exact Hd].
       -- eapply (ic_map (fun x => F a' b' c' d' x)); [intros; eapply H5; eauto|intros; eapply P5; eauto|exact He].
Qed.

Lemma ic_translate_mus : forall S S',
  instance_conv (instance_translate S) (instance_translate S') ->
  instance_conv (instance_translate (TMuS S)) (instance_translate (TMuS S')).
Proof.
  intros S S' H.
  cbn [instance_translate].
  pose proof (ic_lift _ _ H 1 0) as Hl.
  assert (Hp : instance_conv
      (TPair
        (TFst (TApp (lift 1 0 (instance_translate S)) (TVar 0)))
        (TSnd (TApp (lift 1 0 (instance_translate S)) (TVar 0))))
      (TPair
        (TFst (TApp (lift 1 0 (instance_translate S')) (TVar 0)))
        (TSnd (TApp (lift 1 0 (instance_translate S')) (TVar 0))))).
  { apply (ic_map2 (fun a b => TPair
        (TFst (TApp a (TVar 0))) (TSnd (TApp b (TVar 0))))).
    - intros x y z Hxy. apply fs_pair1. apply fs_fst. apply fs_app1. exact Hxy.
    - intros z x y Hxy. apply fs_pair2. apply fs_snd. apply fs_app1. exact Hxy.
    - intros x y z Hxy. apply pt_pair.
      + apply pt_fst. apply pt_app.
        * exact Hxy.
        * exact (prune_term_refl _).
      + exact (prune_term_refl _).
    - intros z x y Hxy. apply pt_pair.
      + exact (prune_term_refl _).
      + apply pt_snd. apply pt_app.
        * exact Hxy.
        * exact (prune_term_refl _).
    - exact Hl. - exact Hl. }
  apply (ic_map (fun p => TLam (TApp (TMuS p) (TVar 0)))).
  - intros x y Hxy. apply fs_lam. apply fs_app1. apply fs_mus. exact Hxy.
  - intros x y Hxy. apply pt_lam. apply pt_app.
    + apply pt_mus. exact Hxy.
    + exact (prune_term_refl _).
  - exact Hp.
Qed.
End _luna_instance_conversion.

(* Checked signature-transport component: _luna_instance_step_prune. *)
Module _luna_instance_step_prune.
Import _parent_instance_pruning.
Import ListNotations TypeRulesCore.

Lemma prune_branches_nth_fwd : forall bs bs' k c b,
  prune_branches bs bs' -> nth_error bs k = Some (c,b) ->
  exists c' b', nth_error bs' k = Some (c',b') /\
    prune_term c c' /\ prune_term b b'.
Proof.
  intros bs bs' k c b H. revert k c b. induction H; intros k x y Hn; destruct k; cbn in Hn.
  - discriminate.
  - discriminate.
  - inversion Hn; subst. eexists; eexists; repeat split; eauto.
  - destruct (IHprune_branches k x y Hn) as [x' [y' [Hxy [Hx Hy]]]].
    exists x',y'. repeat split; cbn; eauto.
Qed.

Lemma prune_branches_nth_bwd : forall bs bs' k c' b',
  prune_branches bs bs' -> nth_error bs' k = Some (c',b') ->
  exists c b, nth_error bs k = Some (c,b) /\
    prune_term c c' /\ prune_term b b'.
Proof.
  intros bs bs' k c' b' H. revert k c' b'. induction H; intros k x y Hn; destruct k; cbn in Hn.
  - discriminate.
  - discriminate.
  - inversion Hn; subst. eexists; eexists; repeat split; eauto.
  - destruct (IHprune_branches k x y Hn) as [x' [y' [Hxy [Hx Hy]]]].
    exists x',y'. repeat split; cbn; eauto.
Qed.

Lemma prune_branches_app_inv : forall pre suf out,
  prune_branches (pre ++ suf) out ->
  exists pre' suf', out = pre' ++ suf' /\
    prune_branches pre pre' /\ prune_branches suf suf'.
Proof.
  intros pre. induction pre as [|[c b] pre IH]; intros suf out H.
  - exists [], out. split; [reflexivity|]. split; [apply pb_nil|exact H].
  - cbn in H. inversion H as [|c0 c1 b0 b1 bs0 bs1 Hc Hb Htail]; subst.
    destruct (IH _ _ Htail) as [pre' [suf' [-> [Hp Hs]]]].
    exists ((c1,b1)::pre'), suf'. repeat split; eauto.
  all: constructor; eauto.
Qed.

Lemma prune_branches_app : forall pre pre' suf suf',
  prune_branches pre pre' -> prune_branches suf suf' ->
  prune_branches (pre ++ suf) (pre' ++ suf').
Proof.
  intros pre pre' suf suf' H. induction H; intros Hs; cbn; eauto using prune_branches.
Qed.

Lemma prune_enum_pos : forall c n d,
  enum_pos c n -> prune_term c d -> d = c.
Proof.
  intros c n d H. revert d. induction H as [|c n H IH]; intros d Hp.
  - inversion Hp; reflexivity.
  - inversion Hp; subst. f_equal.
    apply IH; assumption.
Qed.
End _luna_instance_step_prune.

(* Checked signature-transport component: _parent_instance_translation. *)
Module _parent_instance_translation.
Import SignatureInstances _parent_instance_pruning _luna_instance_conversion _luna_instance_step_prune.
Import ListNotations TypeRulesCore.

Ltac ic_congruence :=
  first [apply (ic_map TSort)|apply (ic_map TLam)|apply (ic_map TFst)|
    apply (ic_map TSnd)|apply (ic_map TEnumT)|apply (ic_map TESucc)|
    apply (ic_map TIDesc)|apply (ic_map TIVar)|apply (ic_map TMuI)|
    apply (ic_map TIn)|apply (ic_map TList)|apply (ic_map TLNil)|
    apply (ic_map2 TPi)|apply (ic_map2 TApp)|apply (ic_map2 TSigma)|
    apply (ic_map2 TPair)|apply (ic_map2 TConsE)|apply (ic_map2 TEPi)|
    apply (ic_map2 TIProd)|apply (ic_map2 TIPi)|apply (ic_map2 TISig)|
    apply (ic_map2 TIChoice)|apply (ic_map2 TInterp)|apply (ic_map3 TLCons)|
    apply (ic_map4 TSwitch)|apply (ic_map4 TIAll)|apply (ic_map5 TInd)|apply (ic_map5 THyps)];
  intros; try assumption;
  try solve [constructor; assumption];
  try solve [constructor; first [assumption|apply prune_term_refl]].

Lemma instance_translate_conv_parent : forall t u, conv t u ->
  instance_conv (instance_translate t) (instance_translate u).
Proof.
  intros t u H. induction H;
    try solve [cbn [instance_translate]; ic_congruence].
  - apply ic_core, fc_step, fs_step, instance_translate_step; assumption.
  - apply ic_refl.
  - apply ic_sym; assumption.
  - eapply ic_trans; eassumption.
  - cbn [instance_translate]. rewrite instance_translate_lift. apply ic_core, fc_step, fs_eta.
  - apply ic_translate_mus; assumption.
  - cbn [instance_translate]. apply (ic_map2 (fun M Q => TCase M Q
       (map (fun '(c,b) => (instance_translate c, instance_translate b)) bs)));
      intros; try assumption.
    + apply fs_case1; assumption.
    + apply fs_case2; assumption.
    + apply pt_case; first [assumption|apply prune_term_refl|apply prune_branches_refl].
    + apply pt_case; first [assumption|apply prune_term_refl|apply prune_branches_refl].
  - cbn [instance_translate]. rewrite !map_app. cbn.
    apply (ic_map2 (fun c b => TCase (instance_translate M) (instance_translate Q)
       (map (fun '(c,b) => (instance_translate c, instance_translate b)) bs1 ++
         (c,b) :: map (fun '(c,b) => (instance_translate c, instance_translate b)) bs2)));
      intros; try assumption; try solve [apply fs_case_br1; assumption|apply fs_case_br2; assumption].
    + apply pt_case; try apply prune_term_refl.
      apply prune_branches_app; [apply prune_branches_refl|].
      constructor; first [assumption|apply prune_term_refl|apply prune_branches_refl].
    + apply pt_case; try apply prune_term_refl.
      apply prune_branches_app; [apply prune_branches_refl|].
      constructor; first [assumption|apply prune_term_refl|apply prune_branches_refl].
Qed.
End _parent_instance_translation.

(* Checked signature-transport component: _parent_pruning_diamond. *)
Module _parent_pruning_diamond.
Import SignatureConversion SignatureInstances _parent_instance_pruning.
Import ListNotations TypeRulesCore _work_cjoin.

Definition prune_diamond_at t := forall u v,
  prune_term t u -> prune_term t v ->
  exists w, prune_term u w /\ prune_term v w.
Definition prune_cross_at t := forall B u v,
  prune_labels B t u -> prune_term t v ->
  exists w, prune_term u w /\ prune_labels B v w.
Definition labels_diamond_at t := forall B u v,
  prune_labels B t u -> prune_labels B t v ->
  exists w, prune_labels B u w /\ prune_labels B v w.

Lemma prune_branches_diamond_from : forall bs,
  (forall c b, In (c,b) bs -> prune_diamond_at c /\ prune_diamond_at b) ->
  forall us vs, prune_branches bs us -> prune_branches bs vs ->
  exists ws, prune_branches us ws /\ prune_branches vs ws.
Proof.
  induction bs as [|[c b] bs IH]; intros HP us vs H1 H2;
    inversion H1; subst; inversion H2; subst.
  - exists []; split; constructor.
  - destruct (HP c b (or_introl eq_refl)) as [HC HB].
    unfold prune_diamond_at in HC, HB.
    destruct (HC _ _ H4 H5) as [cw [HC1 HC2]].
    destruct (HB _ _ H6 H9) as [bw [HB1 HB2]].
    assert (Htail : forall cx bx, In (cx,bx) bs ->
      prune_diamond_at cx /\ prune_diamond_at bx).
    { intros cx bx Hin. apply HP. right; exact Hin. }
    destruct (IH Htail _ _ H7 H10) as [ws [HS1 HS2]].
    exists ((cw,bw)::ws); split; constructor; assumption.
Qed.

Ltac pruning_size := cbn; lia.

Ltac pruning_join_children IH :=
  repeat match goal with
  | H1 : prune_term ?x ?y, H2 : prune_term ?x ?z |- _ =>
    first [constr_eq H1 H2; fail 1 |
      let Hp := fresh "Hp" in
      let w := fresh "w" in let Hy := fresh "Hy" in let Hz := fresh "Hz" in
      pose proof (proj1 (IH x ltac:(pruning_size))) as Hp;
      destruct (Hp _ _ H1 H2) as [w [Hy Hz]];
      clear H1 H2 Hp]
  end.

Ltac pruning_plain IH :=
  intros u v H1 H2; inversion H1; subst; clear H1;
  inversion H2; subst; clear H2;
  pruning_join_children IH;
  eexists; split; constructor; eassumption.

Lemma prune_diamonds_mut : forall t,
  prune_diamond_at t /\ prune_cross_at t /\ labels_diamond_at t.
Proof.
  apply (tsize_strong_ind (fun t =>
    prune_diamond_at t /\ prune_cross_at t /\ labels_diamond_at t)).
  intros t IH.
  assert (HP : prune_diamond_at t).
  { unfold prune_diamond_at. destruct t;
      try solve [pruning_plain IH].
    - (* MuS; only a pair payload permits an instance-pruning rule. *)
      destruct t; try solve [pruning_plain IH].
      intros u v H1 H2.
      destruct (prune_mus_pair_inv _ _ _ H1) as [B1 [L1 [-> [HB1 HL1]]]].
      destruct (prune_mus_pair_inv _ _ _ H2) as [B2 [L2 [-> [HB2 HL2]]]].
      destruct (proj1 (IH t1 ltac:(cbn; lia)) _ _ HB1 HB2)
        as [B3 [HB13 HB23]].
      destruct (proj2 (proj2 (IH t2 ltac:(cbn; lia))) t1 _ _ HL1 HL2)
        as [L3 [HL13 HL23]].
      exists (TMuS (TPair B3 L3)). split; apply pt_instance; try assumption.
      + eapply prune_labels_rebase; [exact HL13|].
        rewrite (prune_erase _ _ HB1). apply cjoin_refl.
      + eapply prune_labels_rebase; [exact HL23|].
        rewrite (prune_erase _ _ HB2). apply cjoin_refl.
    - (* Case branches. *)
      intros u v H1 H2. inversion H1; subst; clear H1.
      inversion H2; subst; clear H2. pruning_join_children IH.
      assert (HB : forall c b, In (c,b) bs ->
        prune_diamond_at c /\ prune_diamond_at b).
      { intros c b Hin. split.
        - apply (proj1 (IH c ltac:(eapply tsize_case_bs; exact Hin))).
        - apply (proj1 (IH b ltac:(eapply tsize_case_bs_body; exact Hin))). }
      destruct (prune_branches_diamond_from bs HB _ _ H7 H9)
        as [ws [HS1 HS2]].
      exists (TCase w0 w ws). split; constructor; eassumption. }
  assert (HC : prune_cross_at t).
  { unfold prune_cross_at. intros B u v HL HT.
    inversion HL; subst.
    - destruct (HP _ _ ltac:(eassumption) HT) as [w [Hw1 Hw2]].
      exists w. split; [exact Hw1|apply pl_stop; exact Hw2].
    - inversion HT; subst; clear HT.
      destruct (proj1 (IH A ltac:(cbn; lia)) _ _ H H5)
        as [Aw [HA1 HA2]].
      destruct (proj1 (IH c ltac:(cbn; lia)) _ _ H0 H7)
        as [cw [Hc1 Hc2]].
      destruct (proj1 (proj2 (IH L ltac:(cbn; lia))) B _ _ H1 H8)
        as [Lw [HL1 HL2]].
      exists (TLCons Aw cw Lw). split; [apply pt_lcons|apply pl_keep]; assumption.
    - inversion HT; subst; clear HT.
      destruct (proj1 (proj2 (IH L ltac:(cbn; lia))) B _ _ H0 H7)
        as [Lw [HL1 HL2]].
      exists Lw. split; [exact HL1|]. apply pl_drop; [|exact HL2].
      eapply instance_dead_join; [|exact H].
      cbn. rewrite (prune_erase _ _ H6). apply cjoin_refl. }
  split; [exact HP|]. split; [exact HC|].
  unfold labels_diamond_at. intros B u v H1 H2.
  inversion H1; subst.
  - destruct (HC B _ _ H2 ltac:(eassumption)) as [w [Hv Hu]].
    exists w. split; [exact Hu|apply pl_stop; exact Hv].
  - inversion H2; subst.
    + destruct (HC B _ _ H1 ltac:(eassumption)) as [w [Hu Hv]].
      exists w. split; [apply pl_stop; exact Hu|exact Hv].
    + destruct (proj1 (IH A ltac:(cbn; lia)) _ _ H H8)
        as [Aw [HA1 HA2]].
      destruct (proj1 (IH c ltac:(cbn; lia)) _ _ H0 H10)
        as [cw [Hc1 Hc2]].
      destruct (proj2 (proj2 (IH L ltac:(cbn; lia))) B _ _ H3 H11)
        as [Lw [HL1 HL2]].
      exists (TLCons Aw cw Lw). split; apply pl_keep; assumption.
    + destruct (proj2 (proj2 (IH L ltac:(cbn; lia))) B _ _ H3 H10)
        as [Lw [HL1 HL2]].
      exists Lw. split; [|exact HL2]. apply pl_drop; [|exact HL1].
      eapply instance_dead_join; [|exact H9].
      cbn. rewrite (prune_erase _ _ H0). apply cjoin_refl.
  - inversion H2; subst.
    + destruct (HC B _ _ H1 ltac:(eassumption)) as [w [Hu Hv]].
      exists w. split; [apply pl_stop; exact Hu|exact Hv].
    + destruct (proj2 (proj2 (IH L ltac:(cbn; lia))) B _ _ H0 H10)
        as [Lw [HL1 HL2]].
      exists Lw. split; [exact HL1|]. apply pl_drop; [|exact HL2].
      eapply instance_dead_join; [|exact H].
      cbn. rewrite (prune_erase _ _ H9). apply cjoin_refl.
    + exact (proj2 (proj2 (IH L ltac:(cbn; lia))) B _ _ H0 H9).
Qed.

Theorem prune_term_diamond : diamond prune_term.
Proof. intros t u v H1 H2. exact (proj1 (prune_diamonds_mut t) u v H1 H2). Qed.
Theorem prune_term_confluent : confluent prune_term.
Proof. apply diamond_rtc_confluent, prune_term_diamond. Qed.
End _parent_pruning_diamond.

(* Checked signature-transport component: _parent_pruning_lower. *)
Module _parent_pruning_lower.
Import _parent_instance_pruning.
Import ListNotations TypeRulesCore _tmp_lower.

Ltac pruning_lower_source :=
  repeat match goal with
  | H : ?lhs = Some _ |- _ =>
    lazymatch lhs with
    | context [option_map ?F ?x] => destruct x eqn:?; cbn in H; try discriminate
    | context [match ?x with Some _ => _ | None => _ end] =>
        destruct x eqn:?; cbn in H; try discriminate
    end
  end.

Ltac pruning_lower_ih :=
  repeat match goal with
  | IH : forall k t0, lower k ?t = Some t0 -> exists u0, lower k ?u = Some u0,
    H : lower ?kk ?t = Some ?t0 |- _ =>
      let w := fresh "w" in let Hw := fresh "Hw" in
      destruct (IH kk t0 H) as [w Hw]; clear IH
  | IH : forall k bs0, lower_bs lower k ?bs = Some bs0 ->
        exists us0, lower_bs lower k ?us = Some us0,
    H : lower_bs lower ?kk ?bs = Some ?bs0 |- _ =>
      let w := fresh "w" in let Hw := fresh "Hw" in
      destruct (IH kk bs0 H) as [w Hw]; clear IH
  end.

Lemma prune_lower_mut :
  (forall t u, prune_term t u -> forall k t0,
    lower k t = Some t0 -> exists u0, lower k u = Some u0) /\
  (forall bs us, prune_branches bs us -> forall k bs0,
    lower_bs lower k bs = Some bs0 ->
    exists us0, lower_bs lower k us = Some us0) /\
  (forall B L L', prune_labels B L L' -> forall k L0,
    lower k L = Some L0 -> exists L'0, lower k L' = Some L'0).
Proof.
  apply prune_mut_ind; intros;
    try solve [eexists; eassumption];
    cbn [lower lower_bs] in *;
    pruning_lower_source; pruning_lower_ih;
    try solve [repeat match goal with H : ?x = Some _ |- _ => rewrite H end;
      eexists; reflexivity].
Qed.

Lemma pruning_lower_bs_sound : forall bs k cs,
  (forall c b, In (c,b) bs ->
    (forall c0, lower k c = Some c0 -> lift 1 k c0 = c) /\
    (forall b0, lower (S k) b = Some b0 -> lift 1 (S k) b0 = b)) ->
  lower_bs lower k bs = Some cs ->
  map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) cs = bs.
Proof.
  induction bs as [|[c b] bs IH]; intros k cs HP HL; cbn in HL.
  - inversion HL. reflexivity.
  - destruct (lower k c) as [c0|] eqn:HC; [|discriminate].
    destruct (lower (S k) b) as [b0|] eqn:HB; [|discriminate].
    destruct (lower_bs lower k bs) as [cs0|] eqn:HS; [|discriminate].
    inversion HL; subst cs. cbn.
    destruct (HP c b (or_introl eq_refl)) as [Hc Hb].
    rewrite (Hc c0 HC), (Hb b0 HB).
    f_equal. apply IH; [|exact HS].
    intros cx bx Hin. apply HP. right; exact Hin.
Qed.

Lemma pruning_lower_sound : forall u k v,
  lower k u = Some v -> lift 1 k v = u.
Proof.
  apply (tsize_strong_ind
    (fun u => forall k v, lower k u = Some v -> lift 1 k v = u)).
  intros u IH k v Hlow. destruct u; cbn [lower] in Hlow.
  all: try solve [
    repeat match type of Hlow with
    | context [lower ?kk ?uu] =>
        let E := fresh "E" in destruct (lower kk uu) eqn:E
    end;
    try discriminate;
    inversion Hlow; subst v; cbn [lift];
    repeat match goal with
    | E : lower ?kk ?uu = Some ?vv |- _ =>
      rewrite (IH uu ltac:(cbn; lia) kk vv E)
    end; reflexivity].
  - cbv [lower] in Hlow.
    destruct (n <? k) eqn:Hlt.
    + inversion Hlow. cbv [lift]. rewrite Hlt. reflexivity.
    + destruct (n =? k) eqn:Heq; [discriminate|].
      inversion Hlow. cbv [lift].
      assert (Hge : k <= n) by (apply Nat.ltb_ge; exact Hlt).
      assert (Hneq : n <> k) by (apply Nat.eqb_neq; exact Heq).
      assert (Hpred : (Nat.pred n <? k) = false) by
        (apply Nat.ltb_ge; destruct n; cbn in *; lia).
      rewrite Hpred. f_equal. lia.
  - destruct (lower k u1) as [M0|] eqn:HM; [|discriminate].
  destruct (lower k u2) as [Q0|] eqn:HQ; [|discriminate].
  destruct (lower_bs lower k bs) as [bs0|] eqn:HB; [|discriminate].
  inversion Hlow; subst v. cbn [lift].
  rewrite (IH u1 ltac:(cbn; lia) k M0 HM).
  rewrite (IH u2 ltac:(cbn; lia) k Q0 HQ).
  f_equal. apply pruning_lower_bs_sound; [|exact HB].
  intros c b Hin. split; intros x Hx.
    + apply (IH c ltac:(eapply tsize_case_bs; exact Hin) k x Hx).
    + apply (IH b ltac:(eapply tsize_case_bs_body; exact Hin) (S k) x Hx).
Qed.

Lemma prune_lift1_descent : forall t u,
  prune_term (lift 1 0 t) u ->
  exists u0, u = lift 1 0 u0 /\ prune_term t u0.
Proof.
  intros t u H.
  destruct (proj1 prune_lower_mut _ _ H 0 t (lower_lift 0 t))
    as [u0 Hu0].
  exists u0. split; [symmetry; exact (pruning_lower_sound u 0 u0 Hu0)|].
  pose proof (prune_subst _ _ (TVar 0) (TVar 0) 0 H (pt_var 0)) as HS.
  rewrite <- (pruning_lower_sound u 0 u0 Hu0) in HS.
  rewrite !subst_lift_zero in HS. exact HS.
Qed.
End _parent_pruning_lower.

(* Checked signature-transport component: _parent_step_prune. *)
Module _parent_step_prune.
Import _parent_instance_pruning _luna_instance_step_prune.
Import ListNotations TypeRulesCore.

Ltac pruning_inv_data :=
  repeat match goal with
  | H : prune_term (TLam _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TPair _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIn _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TConsE _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term TNilE _ |- _ => inversion H; subst; clear H
  | H : prune_term TEZero _ |- _ => inversion H; subst; clear H
  | H : prune_term (TESucc _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIVar _) _ |- _ => inversion H; subst; clear H
  | H : prune_term TI1 _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIProd _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIPi _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TISig _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term (TIChoice _ _) _ |- _ => inversion H; subst; clear H
  | H : prune_term TUnit _ |- _ => inversion H; subst; clear H
  end.

Ltac pruning_use_step_ih :=
  match goal with
  | IH : forall v, prune_term ?src v -> exists w, step v w /\ prune_term ?dst w,
    Hp : prune_term ?src ?v |- _ =>
    destruct (IH v Hp) as [w [Hw HPw]];
    eexists; split; [constructor; exact Hw|constructor; eassumption]
  end.

Lemma step_prune_sim_parent : forall t u, step t u -> forall v,
  prune_term t v -> exists w, step v w /\ prune_term u w.
Proof.
  intros t u H. induction H; intros v Hp; inversion Hp; subst; clear Hp;
    pruning_inv_data;
    try solve [pruning_use_step_ih];
    try solve [eexists; split; [constructor|
      eauto 10 using prune_term, prune_lift, prune_subst]].
  - eexists. split; [apply st_ind|].
    repeat first [assumption | apply prune_lift; assumption | constructor].
  - destruct (prune_branches_nth_fwd bs bs' k c b H9 H)
      as [c1 [b1 [Hnth [Hpc Hpb]]]].
    pose proof (prune_enum_pos c n c1 H0 Hpc) as Ec. subst c1.
    pose proof (prune_enum_pos a n a' H1 H6) as Ea. subst a'.
    exists (subst b' 0 b1). split.
    + eapply st_case with (k:=k) (c:=c) (b:=b1) (n:=n);
        [exact Hnth|exact H0|exact H1|].
      intros j cj bj Hj Hnj.
      destruct (prune_branches_nth_bwd bs bs' j cj bj H9 Hnj)
        as [cj0 [bj0 [Hnj0 [Hcj Hbj]]]].
      destruct (H2 j cj0 bj0 Hj Hnj0) as [nj [HPj Hneq]].
      exists nj. split; [|exact Hneq].
      rewrite (prune_enum_pos cj0 nj cj HPj Hcj). exact HPj.
    + apply prune_subst; assumption.
  - destruct (prune_branches_app_inv bs1 ((c,b)::bs2) bs' H6)
      as [pre [suf [-> [Hpre Hsuf]]]].
    inversion Hsuf as [|cx cy bx bv ts us Hpc Hpb Htail]; subst; clear Hsuf.
    destruct (IHstep cy Hpc) as [cw [Hcw Hpcw]].
    exists (TCase M' Q' (pre ++ (cw,bv)::us)). split.
    + apply st_case_lbl; exact Hcw.
    + apply pt_case; [exact H3|exact H5|].
      apply prune_branches_app; [exact Hpre|]. constructor; assumption.
Qed.
End _parent_step_prune.

(* Checked signature-transport component: _parent_pruning_commute. *)
Module _parent_pruning_commute.
Import SignatureConversion _parent_instance_pruning _parent_pruning_lower _luna_instance_step_prune _parent_step_prune.
Import ListNotations TypeRulesCore _tmp_epstep _work_cjoin.

Lemma pruning_fstep_pair_inv : forall B L u, fstep (TPair B L) u ->
  (exists B', u = TPair B' L /\ fstep B B') \/
  (exists L', u = TPair B L' /\ fstep L L').
Proof.
  intros B L u H. inversion H; subst;
    try solve [match goal with Hs : step (TPair _ _) _ |- _ =>
      inversion Hs; subst; eauto using fstep end]; eauto.
Qed.

Definition prune_core_at t := forall u, fstep t u -> forall v,
  prune_term t v -> exists w, rtc fstep v w /\ prune_term u w.
Definition labels_core_at t := forall B u, fstep t u -> forall v,
  prune_labels B t v -> exists w, rtc fstep v w /\ prune_labels B u w.

Ltac pruning_rtc_context :=
  match goal with
  | HR : rtc fstep ?a ?b |- exists w, rtc fstep ?v w /\ _ =>
    let p := eval pattern a in v in
    lazymatch p with
    | ?F _ => exists (F b); split;
      [apply (rtc_map_parent fstep fstep F); [intros; constructor; assumption|exact HR]
      |constructor; eassumption]
    end
  end.

Ltac pruning_fstep_plain IH Hpr :=
  inversion Hpr; subst; clear Hpr;
  match goal with
  | Hf : fstep ?x ?y, HP : prune_term ?x ?v |- _ =>
    destruct (proj1 (IH x ltac:(cbn; lia)) y Hf v HP) as [w [HR HPw]];
    pruning_rtc_context
  end.

Section WithWeakSimulation.
Variable Hweak : forall t u, step t u -> forall v,
  prune_term t v -> exists w, step v w /\ prune_term u w.

Lemma pruning_core_commute_mut : forall t,
  prune_core_at t /\ labels_core_at t.
Proof.
  apply (tsize_strong_ind (fun t => prune_core_at t /\ labels_core_at t)).
  intros t IH.
  assert (HP : prune_core_at t).
  { unfold prune_core_at. intros u Hf v Hpr. destruct Hf;
      try solve [pruning_fstep_plain IH Hpr].
    - destruct (Hweak _ _ H v Hpr) as [w [Hw HPw]].
      exists w. split; [apply rtc_one, fs_step; exact Hw|exact HPw].
    - inversion Hpr; subst; clear Hpr.
      match goal with HH : prune_term (TApp _ _) _ |- _ => inversion HH; subst; clear HH end.
      match goal with HH : prune_term (TVar 0) _ |- _ => inversion HH; subst; clear HH end.
      match goal with HH : prune_term (lift 1 0 ?f) ?g |- _ =>
        destruct (prune_lift1_descent f g HH) as [g0 [-> Hg0]];
        exists g0; split; [apply rtc_one, fs_eta|exact Hg0]
      end.
    - inversion Hpr; subst; clear Hpr.
      + match goal with Hq : prune_term ?S ?V |- _ =>
          destruct (proj1 (IH S ltac:(cbn; lia)) _ Hf V Hq)
            as [w [HR HPw]];
          exists (TMuS w); split;
          [eapply (rtc_map_parent fstep fstep TMuS); [intros; apply fs_mus; eassumption|exact HR]
          |apply pt_mus; exact HPw]
        end.
      + destruct (pruning_fstep_pair_inv B L S' Hf)
          as [[Bnew [-> HB]]|[Lnew [-> HL]]].
        * destruct (proj1 (IH B ltac:(cbn; lia)) _ HB B' H0)
            as [Bw [HR HPw]].
          exists (TMuS (TPair Bw L')). split.
          -- eapply (rtc_map_parent fstep fstep (fun z => TMuS (TPair z L')));
               [intros; apply fs_mus, fs_pair1; eassumption|exact HR].
          -- apply pt_instance; [exact HPw|].
             eapply prune_labels_rebase; [exact H1|].
             apply conv_phi_cjoin, fstep_conv; exact HB.
        * destruct (proj2 (IH L ltac:(cbn; lia)) B _ HL L' H1)
            as [Lw [HR HPw]].
          exists (TMuS (TPair B' Lw)). split.
          -- eapply (rtc_map_parent fstep fstep (fun z => TMuS (TPair B' z)));
               [intros; apply fs_mus, fs_pair2; eassumption|exact HR].
          -- apply pt_instance; assumption.
    - inversion Hpr; subst; clear Hpr.
      match goal with Hb : prune_branches (bs1 ++ (c,b)::bs2) ?out |- _ =>
        destruct (prune_branches_app_inv bs1 ((c,b)::bs2) out Hb)
          as [pre [suf [-> [Hpre Hsuf]]]];
        inversion Hsuf; subst; clear Hsuf
      end.
      assert (Hszc : tsize c < tsize (TCase M Q (bs1 ++ (c,b)::bs2))).
      { eapply tsize_case_bs. apply in_or_app. right; left; reflexivity. }
      destruct (proj1 (IH c Hszc) _ Hf _ H3) as [cw [HR HPw]].
      exists (TCase M' Q' (pre ++ (cw,b')::bs')). split.
      + eapply (rtc_map_parent fstep fstep
          (fun z => TCase M' Q' (pre ++ (z,b')::bs')));
          [intros; apply fs_case_br1; eassumption|exact HR].
      + apply pt_case; [exact H2|exact H4|].
        apply prune_branches_app; [exact Hpre|]. constructor; assumption.
    - inversion Hpr; subst; clear Hpr.
      destruct (prune_branches_app_inv bs1 ((c,b)::bs2) bs' H5)
        as [pre [suf [-> [Hpre Hsuf]]]].
      inversion Hsuf as [|cx cy bx bv ts us Hpc Hpb Htail]; subst; clear Hsuf.
      assert (Hszb : tsize b < tsize (TCase M Q (bs1 ++ (c,b)::bs2))).
      { eapply tsize_case_bs_body. apply in_or_app. right; left; reflexivity. }
      destruct (proj1 (IH b Hszb) _ Hf _ Hpb) as [bw [HR HPw]].
      exists (TCase M' Q' (pre ++ (cy,bw)::us)). split.
      + eapply (rtc_map_parent fstep fstep
          (fun z => TCase M' Q' (pre ++ (cy,z)::us)));
          [intros; apply fs_case_br2; eassumption|exact HR].
      + apply pt_case; [exact H2|exact H4|].
        apply prune_branches_app; [exact Hpre|]. constructor; assumption. }
  split; [exact HP|].
  unfold labels_core_at. intros B u Hf v Hpl. inversion Hpl; subst.
  - destruct (HP _ Hf _ ltac:(eassumption)) as [w [HR HPw]].
    exists w. split; [exact HR|apply pl_stop; exact HPw].
  - destruct (fstep_lcons_inv A c L u Hf)
      as [[An [-> HA]]|[[cn [-> HC]]|[Ln [-> HL]]]].
    + destruct (proj1 (IH A ltac:(cbn; lia)) _ HA _ H) as [w [HR Hw]].
      exists (TLCons w c' L'). split.
      * eapply (rtc_map_parent fstep fstep (fun z => TLCons z c' L'));
          [intros; apply fs_lcons1; eassumption|exact HR].
      * apply pl_keep; assumption.
    + destruct (proj1 (IH c ltac:(cbn; lia)) _ HC _ H0) as [w [HR Hw]].
      exists (TLCons A' w L'). split.
      * eapply (rtc_map_parent fstep fstep (fun z => TLCons A' z L'));
          [intros; apply fs_lcons2; eassumption|exact HR].
      * apply pl_keep; assumption.
    + destruct (proj2 (IH L ltac:(cbn; lia)) B _ HL _ H1) as [w [HR Hw]].
      exists (TLCons A' c' w). split.
      * eapply (rtc_map_parent fstep fstep (fun z => TLCons A' c' z));
          [intros; apply fs_lcons3; eassumption|exact HR].
      * apply pl_keep; assumption.
  - destruct (fstep_lcons_inv A c L u Hf)
      as [[An [-> HA]]|[[cn [-> HC]]|[Ln [-> HL]]]].
    + exists v. split; [apply rtc_refl|apply pl_drop; assumption].
    + exists v. split; [apply rtc_refl|]. apply pl_drop; [|assumption].
      eapply instance_dead_join; [|exact H].
      apply conv_phi_cjoin, cv_app; [apply cv_refl|apply fstep_conv; exact HC].
    + destruct (proj2 (IH L ltac:(cbn; lia)) B _ HL _ H0) as [w [HR Hw]].
      exists w. split; [exact HR|apply pl_drop; assumption].
Qed.
End WithWeakSimulation.

Theorem fstep_prune_commute : forall t u v,
  fstep t u -> prune_term t v ->
  exists w, prune_term u w /\ rtc fstep v w.
Proof.
  intros t u v Hf Hp.
  destruct (proj1 (pruning_core_commute_mut step_prune_sim_parent t) u Hf v Hp)
    as [w [HR HP]]. exists w; auto.
Qed.
End _parent_pruning_commute.

(* Checked signature-transport component: _luna_instance_core_paths. *)
Module _luna_instance_core_paths.
Import TypeRulesCore.
Import ListNotations.
Import _tmp_epstep.
Import _work_mixed_closure.
Import _work_cjoin.

Lemma rtc_map_test : forall (F : term -> term) x y,
    (forall a b, fstep a b -> fstep (F a) (F b)) ->
    rtc fstep x y -> rtc fstep (F x) (F y).
Proof.
  intros F x y HF H; induction H as [x|x y z Hxy Hyz IH].
  - apply rtc_refl.
  - eapply rtc_step; [apply HF; exact Hxy | exact IH].
Qed.

Lemma rtc_congr2 : forall (F : term -> term -> term) x x' y y',
    (forall a b, fstep a b -> fstep (F a y) (F b y)) ->
    (forall a b, fstep a b -> fstep (F x' a) (F x' b)) ->
    rtc fstep x x' -> rtc fstep y y' ->
    rtc fstep (F x y) (F x' y').
Proof.
  intros F x x' y y' H1 H2 Hx Hy.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun a => F a y) x x'); eauto.
  - eapply (rtc_map_test (fun b => F x' b) y y'); eauto.
Qed.

Lemma test_pi2 : forall A A' B B', rtc fstep A A' -> rtc fstep B B' ->
    rtc fstep (TPi A B) (TPi A' B').
Proof.
  intros; eapply (rtc_congr2 (fun x y => TPi x y));
    eauto using fs_pi1, fs_pi2.
Qed.

Lemma rtc_congr1 : forall (F : term -> term) x x',
    (forall a b, fstep a b -> fstep (F a) (F b)) ->
    rtc fstep x x' -> rtc fstep (F x) (F x').
Proof. intros; eapply rtc_map_test; eauto. Qed.

Lemma rtc_congr3 : forall (F : term -> term -> term -> term)
    x x' y y' z z',
    (forall a b, fstep a b -> fstep (F a y z) (F b y z)) ->
    (forall a b, fstep a b -> fstep (F x' a z) (F x' b z)) ->
    (forall a b, fstep a b -> fstep (F x' y' a) (F x' y' b)) ->
    rtc fstep x x' -> rtc fstep y y' -> rtc fstep z z' ->
    rtc fstep (F x y z) (F x' y' z').
Proof.
  intros F x x' y y' z z' H1 H2 H3 Hx Hy Hz.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun a => F a y z) x x'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun b => F x' b z) y y'); eauto.
    + eapply (rtc_map_test (fun c => F x' y' c) z z'); eauto.
Qed.

Lemma rtc_congr4 : forall (F : term -> term -> term -> term -> term)
    a a' b b' c c' d d',
    (forall x y, fstep x y -> fstep (F x b c d) (F y b c d)) ->
    (forall x y, fstep x y -> fstep (F a' x c d) (F a' y c d)) ->
    (forall x y, fstep x y -> fstep (F a' b' x d) (F a' b' y d)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' x) (F a' b' c' y)) ->
    rtc fstep a a' -> rtc fstep b b' -> rtc fstep c c' -> rtc fstep d d' ->
    rtc fstep (F a b c d) (F a' b' c' d').
Proof.
  intros F a a' b b' c c' d d' H1 H2 H3 H4 Ha Hb Hc Hd.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun x => F x b c d) a a'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun x => F a' x c d) b b'); eauto.
    + eapply rtc_trans.
      * eapply (rtc_map_test (fun x => F a' b' x d) c c'); eauto.
      * eapply (rtc_map_test (fun x => F a' b' c' x) d d'); eauto.
Qed.

Lemma rtc_congr5 : forall (F : term -> term -> term -> term -> term -> term)
    a a' b b' c c' d d' e e',
    (forall x y, fstep x y -> fstep (F x b c d e) (F y b c d e)) ->
    (forall x y, fstep x y -> fstep (F a' x c d e) (F a' y c d e)) ->
    (forall x y, fstep x y -> fstep (F a' b' x d e) (F a' b' y d e)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' x e) (F a' b' c' y e)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' x) (F a' b' c' d' y)) ->
    rtc fstep a a' -> rtc fstep b b' -> rtc fstep c c' -> rtc fstep d d' -> rtc fstep e e' ->
    rtc fstep (F a b c d e) (F a' b' c' d' e').
Proof.
  intros F a a' b b' c c' d d' e e' H1 H2 H3 H4 H5 Ha Hb Hc Hd He.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun x => F x b c d e) a a'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun x => F a' x c d e) b b'); eauto.
    + eapply rtc_trans.
      * eapply (rtc_map_test (fun x => F a' b' x d e) c c'); eauto.
      * eapply rtc_trans.
        { eapply (rtc_map_test (fun x => F a' b' c' x e) d d'); eauto. }
        { eapply (rtc_map_test (fun x => F a' b' c' d' x) e e'); eauto. }
Qed.

Lemma test_branch : forall bs bs', pbranches bs bs' ->
    (forall c c', pstep c c' -> rtc fstep c c') -> forall M Q pre,
    rtc fstep (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs')).
Proof.
  intros bs bs' Hpb.
  intros HP.
  induction Hpb as [|c c' b b' bs bs' Hc Hb Htail IH];
    intros M Q pre.
  - cbn. apply rtc_refl.
  - cbn [app_assoc].
    pose proof (rtc_congr1
      (fun x => TCase M Q (pre ++ (x,b)::bs)) _ _
      (fun x y H => fs_case_br1 M Q pre x y b bs H) (HP c c' Hc)) as H1.
    pose proof (rtc_congr1
      (fun x => TCase M Q (pre ++ (c',x)::bs)) _ _
      (fun x y H => fs_case_br2 M Q pre c' x y bs H) (HP b b' Hb)) as H2.
    pose proof (IH M Q (pre ++ [(c',b')])) as H3.
    rewrite <- (app_assoc pre [(c',b')] bs) in H3.
    cbn in H3.
    rewrite <- (app_assoc pre [(c',b')] bs') in H3.
    cbn in H3.
    eapply rtc_trans; [exact H1 |].
    eapply rtc_trans; [exact H2 | exact H3].
Qed.

Lemma rtc_congr6 : forall (F : term -> term -> term -> term -> term -> term -> term)
    a a' b b' c c' d d' e e' f f',
    (forall x y, fstep x y -> fstep (F x b c d e f) (F y b c d e f)) ->
    (forall x y, fstep x y -> fstep (F a' x c d e f) (F a' y c d e f)) ->
    (forall x y, fstep x y -> fstep (F a' b' x d e f) (F a' b' y d e f)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' x e f) (F a' b' c' y e f)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' x f) (F a' b' c' d' y f)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' e' x) (F a' b' c' d' e' y)) ->
    rtc fstep a a' -> rtc fstep b b' -> rtc fstep c c' -> rtc fstep d d' -> rtc fstep e e' -> rtc fstep f f' ->
    rtc fstep (F a b c d e f) (F a' b' c' d' e' f').
Proof.
  intros F a a' b b' c c' d d' e e' f f' H1 H2 H3 H4 H5 H6 Ha Hb Hc Hd He Hf.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun x => F x b c d e f) a a'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun x => F a' x c d e f) b b'); eauto.
    + eapply rtc_trans.
      * eapply (rtc_map_test (fun x => F a' b' x d e f) c c'); eauto.
      * eapply rtc_trans.
        { eapply (rtc_map_test (fun x => F a' b' c' x e f) d d'); eauto. }
        { eapply rtc_trans.
          - eapply (rtc_map_test (fun x => F a' b' c' d' x f) e e'); eauto.
          - eapply (rtc_map_test (fun x => F a' b' c' d' e' x) f f'); eauto. }
Qed.

Lemma rtc_case_body_nth : forall bs k c b b',
    nth_error bs k = Some (c,b) -> rtc fstep b b' ->
    exists bs', nth_error bs' k = Some (c,b') /\
      (forall j cj bj, j < k -> nth_error bs j = Some (cj,bj) ->
        nth_error bs' j = Some (cj,bj)) /\
      forall M Q pre, rtc fstep (TCase M Q (pre ++ bs))
        (TCase M Q (pre ++ bs')).
Proof.
  intros bs. induction bs as [|[c0 b0] bs IH];
    intros [|k] c b b' Hnth Hb.
  - discriminate.
  - discriminate.
  - cbn in Hnth. inversion Hnth; subst c b.
    exists ((c0,b')::bs). split; [reflexivity|]. split.
    + intros j cj bj Hj. lia.
    +
    intros M Q pre.
    eapply (rtc_congr1
      (fun x => TCase M Q (pre ++ (c0,x)::bs)) _ _
      (fun x y H => fs_case_br2 M Q pre c0 x y bs H) Hb).
  - cbn in Hnth.
    destruct (IH k c b b' Hnth Hb) as [bs' [Hidx [Hpres Hpath]]].
    exists ((c0,b0)::bs'). split; [exact Hidx|]. split.
    + intros j cj bj Hj Horig. destruct j as [|j].
      * cbn in Horig. inversion Horig; subst. cbn. reflexivity.
      * cbn in Horig. cbn. apply Hpres; [lia|exact Horig].
    + intros M Q pre.
    pose proof (Hpath M Q (pre ++ [(c0,b0)])) as H.
    rewrite <- (app_assoc pre [(c0,b0)] bs) in H.
    cbn in H.
    rewrite <- (app_assoc pre [(c0,b0)] bs') in H.
    cbn in H.
    exact H.
Qed.

Lemma test_switche : forall E P p x y,
 fstep x y -> fstep (TSwitch E P p (TESucc x)) (TSwitch E P p (TESucc y)).
Proof. intros; eapply fs_switch4; eapply fs_esucc; eauto. Qed.

Lemma branch_cons : forall c c' b b' bs bs',
    rtc fstep c c' -> rtc fstep b b' ->
    (forall M Q pre, rtc fstep (TCase M Q (pre ++ bs))
      (TCase M Q (pre ++ bs'))) ->
    forall M Q pre, rtc fstep
      (TCase M Q (pre ++ (c,b)::bs))
      (TCase M Q (pre ++ (c',b')::bs')).
Proof.
  intros c c' b b' bs bs' Hc Hb Htail M Q pre.
  pose proof (rtc_congr1
    (fun x => TCase M Q (pre ++ (x,b)::bs)) _ _
    (fun x y H => fs_case_br1 M Q pre x y b bs H) Hc) as H1.
  pose proof (rtc_congr1
    (fun x => TCase M Q (pre ++ (c',x)::bs)) _ _
    (fun x y H => fs_case_br2 M Q pre c' x y bs H) Hb) as H2.
  pose proof (Htail M Q (pre ++ [(c',b')])) as H3.
  rewrite <- (app_assoc pre [(c',b')] bs) in H3; cbn in H3.
  rewrite <- (app_assoc pre [(c',b')] bs') in H3; cbn in H3.
  eapply rtc_trans; [exact H1|].
  eapply rtc_trans; [exact H2|exact H3].
Qed.

Lemma rtc_congr7 : forall (F : term -> term -> term -> term -> term -> term -> term -> term)
    a a' b b' c c' d d' e e' f f' g g',
    (forall x y, fstep x y -> fstep (F x b c d e f g) (F y b c d e f g)) ->
    (forall x y, fstep x y -> fstep (F a' x c d e f g) (F a' y c d e f g)) ->
    (forall x y, fstep x y -> fstep (F a' b' x d e f g) (F a' b' y d e f g)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' x e f g) (F a' b' c' y e f g)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' x f g) (F a' b' c' d' y f g)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' e' x g) (F a' b' c' d' e' y g)) ->
    (forall x y, fstep x y -> fstep (F a' b' c' d' e' f' x) (F a' b' c' d' e' f' y)) ->
    rtc fstep a a' -> rtc fstep b b' -> rtc fstep c c' -> rtc fstep d d' ->
    rtc fstep e e' -> rtc fstep f f' -> rtc fstep g g' ->
    rtc fstep (F a b c d e f g) (F a' b' c' d' e' f' g').
Proof.
  intros F a a' b b' c c' d d' e e' f f' g g' H1 H2 H3 H4 H5 H6 H7 Ha Hb Hc Hd He Hf Hg.
  eapply rtc_trans.
  - eapply (rtc_map_test (fun x => F x b c d e f g) a a'); eauto.
  - eapply rtc_trans.
    + eapply (rtc_map_test (fun x => F a' x c d e f g) b b'); eauto.
    + eapply rtc_trans.
      * eapply (rtc_map_test (fun x => F a' b' x d e f g) c c'); eauto.
      * eapply rtc_trans.
        { eapply (rtc_map_test (fun x => F a' b' c' x e f g) d d'); eauto. }
        { eapply rtc_trans.
          - eapply (rtc_map_test (fun x => F a' b' c' d' x f g) e e'); eauto.
          - eapply rtc_trans.
            + eapply (rtc_map_test (fun x => F a' b' c' d' e' x g) f f'); eauto.
            + eapply (rtc_map_test (fun x => F a' b' c' d' e' f' x) g g'); eauto. }
Qed.

Lemma rtc_case_body_nth_strong : forall bs k c b b',
    nth_error bs k = Some (c,b) -> rtc fstep b b' ->
    exists bs', nth_error bs' k = Some (c,b') /\
      (forall j, j < k -> nth_error bs' j = nth_error bs j) /\
      (forall M Q pre, rtc fstep (TCase M Q (pre ++ bs))
        (TCase M Q (pre ++ bs'))).
Proof.
  intros bs. induction bs as [|[c0 b0] bs IH]; intros [|k] c b b' Hnth Hb;
    try discriminate.
  - cbn in Hnth. inversion Hnth; subst.
    exists ((c,b')::bs). split; [reflexivity|]. split.
    + intros j Hj; lia.
    + intros M Q pre.
      eapply rtc_congr1 with
        (F := fun x => TCase M Q (pre ++ (c,x)::bs)).
      * intros x y H; cbn [app_assoc]; exact (fs_case_br2 M Q pre c x y bs H).
      * exact Hb.
  - cbn in Hnth.
    destruct (IH k c b b' Hnth Hb) as [bs' [Hi [Heq Hp]]].
    exists ((c0,b0)::bs'). split; [exact Hi|]. split.
    + intros [|j] Hj.
      * reflexivity.
      * cbn. apply Heq; lia.
    + intros M Q pre.
    pose proof (Hp M Q (pre ++ [(c0,b0)])) as H.
    rewrite <- (app_assoc pre [(c0,b0)] bs) in H; cbn in H.
    rewrite <- (app_assoc pre [(c0,b0)] bs') in H; cbn in H.
      exact H.
Qed.

Lemma test_mut :
  (forall t u, pstep t u -> rtc fstep t u) /\
  (forall bs bs', pbranches bs bs' -> forall M Q pre,
    rtc fstep (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply pstep_pbranches_ind; cbn; intros.
  all: try solve [apply rtc_refl].
  all: try solve [eapply (rtc_congr1 (fun x => TLam x)); eauto using fs_lam].
  all: try solve [eapply (rtc_congr1 (fun x => TFst x)); eauto using fs_fst].
  all: try solve [eapply (rtc_congr1 (fun x => TSnd x)); eauto using fs_snd].
  all: try solve [eapply (rtc_congr1 (fun x => TEnumT x)); eauto using fs_enumt].
  all: try solve [eapply (rtc_congr1 (fun x => TESucc x)); eauto using fs_esucc].
  all: try solve [eapply (rtc_congr1 (fun x => TIDesc x)); eauto using fs_idesc].
  all: try solve [eapply (rtc_congr1 (fun x => TIVar x)); eauto using fs_ivar].
  all: try solve [eapply (rtc_congr1 (fun x => TMuI x)); eauto using fs_mui].
  all: try solve [eapply (rtc_congr1 (fun x => TMuS x)); eauto using fs_mus].
  all: try solve [eapply (rtc_congr1 (fun x => TIn x)); eauto using fs_in].
  all: try solve [eapply (rtc_congr1 (fun x => TList x)); eauto using fs_list].
  all: try solve [eapply (rtc_congr1 (fun x => TLNil x)); eauto using fs_lnil].
  all: try solve [eapply (rtc_congr2 (fun x y => TPi x y)); eauto using fs_pi1, fs_pi2].
  all: try solve [eapply (rtc_congr2 (fun x y => TApp x y)); eauto using fs_app1, fs_app2].
  all: try solve [eapply (rtc_congr2 (fun x y => TSigma x y)); eauto using fs_sigma1, fs_sigma2].
  all: try solve [eapply (rtc_congr2 (fun x y => TPair x y)); eauto using fs_pair1, fs_pair2].
  all: try solve [eapply (rtc_congr2 (fun x y => TConsE x y)); eauto using fs_conse1, fs_conse2].
  all: try solve [eapply (rtc_congr2 (fun x y => TEPi x y)); eauto using fs_epi1, fs_epi2].
  all: try solve [eapply (rtc_congr2 (fun x y => TIProd x y)); eauto using fs_iprod1, fs_iprod2].
  all: try solve [eapply (rtc_congr2 (fun x y => TIPi x y)); eauto using fs_ipi1, fs_ipi2].
  all: try solve [eapply (rtc_congr2 (fun x y => TISig x y)); eauto using fs_isig1, fs_isig2].
  all: try solve [eapply (rtc_congr2 (fun x y => TIChoice x y)); eauto using fs_ichoice1, fs_ichoice2].
  all: try solve [eapply (rtc_congr2 (fun x y => TInterp x y)); eauto using fs_interp1, fs_interp2].
  all: try solve [eapply (rtc_congr3 (fun x y z => TLCons x y z)); eauto using fs_lcons1, fs_lcons2, fs_lcons3].
  all: try solve [eapply (rtc_congr4 (fun a b c d => TSwitch a b c d)); eauto using fs_switch1, fs_switch2, fs_switch3, fs_switch4].
  all: try solve [eapply (rtc_congr5 (fun a b c d e => TInd a b c d e)); eauto using fs_ind1, fs_ind2, fs_ind3, fs_ind4, fs_ind5].
  all: try solve [eapply (rtc_congr4 (fun a b c d => TIAll a b c d)); eauto using fs_iall1, fs_iall2, fs_iall3, fs_iall4].
  all: try solve [eapply (rtc_congr5 (fun a b c d e => THyps a b c d e)); eauto using fs_hyps1, fs_hyps2, fs_hyps3, fs_hyps4, fs_hyps5].
  all: try match goal with
    |- rtc fstep (TApp (TLam ?b) ?a) (subst ?a' 0 ?b') =>
      idtac "BETA";
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun b a => TApp (TLam b) a))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_case1, fs_case2].
  all: try solve [intros; eauto using fs_case1, fs_case2].
  all: try solve [eauto using fs_lam, fs_app1, fs_app2].
  all: try match goal with
    |- rtc fstep (TFst (TPair ?a ?b)) ?a' =>
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun a b => TFst (TPair a b)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TSnd (TPair ?a ?b)) ?b' =>
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun a b => TSnd (TPair a b)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TEPi TNilE ?P) TUnitT =>
      eapply rtc_trans;
      [eapply (rtc_congr1 (fun P => TEPi TNilE P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TEPi (TConsE ?tg ?E) ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun tg E P => TEPi (TConsE tg E) P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TSwitch (TConsE ?tg ?E) ?P (TPair ?p0 ?ps) TEZero) ?p0' =>
      eapply rtc_trans;
      [eapply (rtc_congr5 (fun tg E P p0 ps => TSwitch (TConsE tg E) P (TPair p0 ps) TEZero))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_pair1, fs_pair2, fs_fst, fs_snd,
    fs_conse1, fs_conse2, fs_epi1, fs_epi2,
    fs_switch1, fs_switch2, fs_switch3, fs_switch4].
  all: try match goal with
    |- rtc fstep (TSwitch (TConsE ?tg ?E) ?P (TPair ?p0 ?ps) (TESucc ?n)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun tg E P p0 ps n => TSwitch (TConsE tg E) P (TPair p0 ps) (TESucc n)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_switch1, fs_switch2, fs_switch3, fs_switch4,
    fs_conse1, fs_conse2, fs_pair1, fs_pair2].
  all: try match goal with
    |- rtc fstep (TIAll (TIVar ?j) ?X ?x ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr4 (fun j X x P => TIAll (TIVar j) X x P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll TI1 ?X TUnit ?P) TUnitT =>
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun X P => TIAll TI1 X TUnit P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll (TIProd ?A ?B) ?X (TPair ?a ?b) ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun A B X a b P => TIAll (TIProd A B) X (TPair a b) P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll (TIPi ?S ?T) ?X ?f ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr5 (fun S T X f P => TIAll (TIPi S T) X f P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll (TISig ?S ?T) ?X (TPair ?s ?x) ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun S T X s x P => TIAll (TISig S T) X (TPair s x) P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TIAll (TIChoice ?E ?T) ?X (TPair ?e ?x) ?P) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun E T X e x P => TIAll (TIChoice E T) X (TPair e x) P))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_iall1, fs_iall2, fs_iall3, fs_iall4,
    fs_ivar, fs_iprod1, fs_iprod2, fs_ipi1, fs_ipi2, fs_isig1, fs_isig2,
    fs_ichoice1, fs_ichoice2, fs_pair1, fs_pair2].
  all: try match goal with
    |- rtc fstep (THyps (TIVar ?j) ?X ?P ?h ?x) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr5 (fun j X P h x => THyps (TIVar j) X P h x))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps TI1 ?X ?P ?h TUnit) TUnit =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun X P h => THyps TI1 X P h TUnit))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps (TIProd ?A ?B) ?X ?P ?h (TPair ?a ?b)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr7 (fun A B X P h a b => THyps (TIProd A B) X P h (TPair a b)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps (TIPi ?S ?T) ?X ?P ?h ?f) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr6 (fun S T X P h f => THyps (TIPi S T) X P h f))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps (TISig ?S ?T) ?X ?P ?h (TPair ?s ?x)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr7 (fun S T X P h s x => THyps (TISig S T) X P h (TPair s x)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (THyps (TIChoice ?E ?T) ?X ?P ?h (TPair ?e ?x)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr7 (fun E T X P h e x => THyps (TIChoice E T) X P h (TPair e x)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_hyps1, fs_hyps2, fs_hyps3, fs_hyps4, fs_hyps5,
    fs_ivar, fs_iprod1, fs_iprod2, fs_ipi1, fs_ipi2, fs_isig1, fs_isig2,
    fs_ichoice1, fs_ichoice2, fs_pair1, fs_pair2].
  all: try match goal with
    |- rtc fstep (TInd ?R ?P ?s ?i (TIn ?xs)) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr5 (fun R P s i xs => TInd R P s i (TIn xs)))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_ind1, fs_ind2, fs_ind3, fs_ind4, fs_ind5, fs_in].
  all: try solve [eapply branch_cons; eauto].
  all: try match goal with
    |- rtc fstep (TCase ?M ?Q ?bs) (TCase ?M' ?Q' ?bs') =>
      eapply rtc_trans;
      [eapply (rtc_congr1 (fun M => TCase M Q bs))
      | eapply rtc_trans;
        [eapply (rtc_congr1 (fun Q => TCase M' Q bs))
        | cbn; eauto]]
    end.
  all: try solve [eauto using fs_case1, fs_case2].
  all: try solve [intros; eauto using fs_case1, fs_case2].
  all: try match goal with
    |- rtc fstep (TInterp (TIVar ?i) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr2 (fun i X => TInterp (TIVar i) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TInterp TI1 ?X) TUnitT =>
      eapply rtc_trans;
      [eapply (rtc_congr1 (fun X => TInterp TI1 X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_interp1, fs_interp2, fs_ivar].
  all: try match goal with
    |- rtc fstep (TInterp (TIProd ?A ?B) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun A B X => TInterp (TIProd A B) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TInterp (TIPi ?S ?T) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun S T X => TInterp (TIPi S T) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TInterp (TISig ?S ?T) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun S T X => TInterp (TISig S T) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try match goal with
    |- rtc fstep (TInterp (TIChoice ?E ?T) ?X) _ =>
      eapply rtc_trans;
      [eapply (rtc_congr3 (fun E T X => TInterp (TIChoice E T) X))
      | eapply rtc_step; [apply fs_step; constructor | apply rtc_refl]]
    end.
  all: try solve [eauto using fs_interp1, fs_interp2, fs_ivar, fs_iprod1, fs_iprod2,
    fs_ipi1, fs_ipi2, fs_isig1, fs_isig2, fs_ichoice1, fs_ichoice2,
    fs_esucc].
  all: try solve [intros x y H; eapply fs_switch4; eapply fs_esucc; exact H].
  all: try eapply test_switche.
  all: try solve [eapply test_branch; eauto].
  all: try solve [eapply test_branch; [eauto | intros; eauto]].
  2: (destruct (rtc_case_body_nth_strong bs k c b b' e H0)
        as [bs' [Hidx' [Hpres Hbody]]];
      eapply rtc_trans;
      [ eapply rtc_congr1
          with (F := fun x => TCase (TIn (TPair a x)) Q bs);
          [ intros; eapply fs_case1; eapply fs_in; eapply fs_pair2; eassumption
          | exact H ]
      | eapply rtc_trans;
        [ exact (Hbody (TIn (TPair a xs')) Q [])
        | eapply rtc_step; [ apply fs_step;
            apply st_case with (k := k) (c := c) (b := b') (n := n);
            [ exact Hidx' | exact e0 | exact e1 |
              intros j cj bj Hj Hnth;
              cbn in Hnth;
              rewrite (Hpres j Hj) in Hnth;
              inversion Hnth; eapply e2; eassumption ]
          | apply rtc_refl ] ] ]).
  1: exact (H1 M' Q' []).
  Qed.

Lemma test_pi : forall A A' B B', rtc fstep A A' -> rtc fstep B B' ->
    rtc fstep (TPi A B) (TPi A' B').
Proof.
  intros A A' B B' HA HB.
  pose proof (rtc_map_test (fun x => TPi x B) A A'
    (fun x y H => fs_pi1 _ _ _ H) HA) as H1.
  pose proof (rtc_map_test (fun x => TPi A' x) B B'
    (fun x y H => fs_pi2 _ _ _ H) HB) as H2.
  eapply rtc_trans; eauto.
Qed.

Lemma test_beta : forall b b' a a', rtc fstep b b' -> rtc fstep a a' ->
 rtc fstep (TApp (TLam b) a) (subst a' 0 b').
Proof.
 intros. eapply rtc_trans.
 - eapply (rtc_congr2 (fun b a => TApp (TLam b) a)); eauto using fs_lam, fs_app1, fs_app2.
 - eapply rtc_step; [apply fs_step; constructor | apply rtc_refl].
Qed.

Lemma pstep_fsteps_instance : forall t u, pstep t u -> rtc fstep t u.
Proof. intros; exact (proj1 (test_mut) t u H). Qed.

Lemma epstep_fsteps_mut :
  (forall t u, epstep t u -> rtc fstep t u) /\
  (forall bs bs', epbranches bs bs' -> forall M Q pre,
    rtc fstep (TCase M Q (pre ++ bs)) (TCase M Q (pre ++ bs'))).
Proof.
  apply _tmp_epstep.epstep_epbranches_ind; cbn; intros.
  all: try solve [apply rtc_refl].
  all: try solve [eapply rtc_congr1; eauto using fs_lam, fs_fst, fs_snd,
    fs_enumt, fs_esucc, fs_idesc, fs_ivar, fs_mui, fs_mus, fs_in,
    fs_list, fs_lnil].
  all: try solve [eapply rtc_congr2; eauto using fs_pi1, fs_pi2,
    fs_app1, fs_app2, fs_sigma1, fs_sigma2, fs_pair1, fs_pair2,
    fs_conse1, fs_conse2, fs_epi1, fs_epi2, fs_iprod1, fs_iprod2,
    fs_ipi1, fs_ipi2, fs_isig1, fs_isig2, fs_ichoice1, fs_ichoice2,
    fs_interp1, fs_interp2].
  all: try solve [eapply rtc_congr3; eauto using fs_lcons1, fs_lcons2, fs_lcons3].
  all: try solve [eapply rtc_congr4; eauto using fs_switch1, fs_switch2,
    fs_switch3, fs_switch4, fs_iall1, fs_iall2, fs_iall3, fs_iall4].
  all: try solve [eapply rtc_congr5; eauto using fs_ind1, fs_ind2, fs_ind3,
    fs_ind4, fs_ind5, fs_hyps1, fs_hyps2, fs_hyps3, fs_hyps4, fs_hyps5].
  all: try match goal with
    |- rtc fstep (TLam (TApp (lift 1 0 ?f) (TVar 0))) ?u =>
      eapply rtc_trans; [eapply rtc_step; [apply fs_eta | apply rtc_refl] | eauto]
    end.
  all: try solve [eapply rtc_congr1; eauto using fs_case1, fs_case2].
  all: try solve [eapply rtc_congr1; eauto using fs_case_br1, fs_case_br2].
  all: try solve [eapply rtc_congr2; eauto using fs_case1, fs_case2].
  1: eapply rtc_trans;
    [ eapply rtc_congr1 with (F := fun x => TCase x Q bs); eauto using fs_case1
    | eapply rtc_trans;
      [ eapply rtc_congr1 with (F := fun x => TCase M' x bs); eauto using fs_case2
      | exact (H1 M' Q' []) ] ].
  all: pose proof (H1 M Q (pre ++ [(c',b')])) as Htail;
    rewrite <- (app_assoc pre [(c',b')] bs) in Htail; cbn in Htail;
    rewrite <- (app_assoc pre [(c',b')] bs') in Htail; cbn in Htail;
    eapply rtc_trans;
    [ eapply rtc_congr1 with
        (F := fun x => TCase M Q (pre ++ (x,b)::bs));
      eauto using fs_case_br1
    | eapply rtc_trans;
      [ eapply rtc_congr1 with
          (F := fun x => TCase M Q (pre ++ (c',x)::bs));
        eauto using fs_case_br2
      | exact Htail ] ].
Qed.

Lemma epstep_fsteps_instance : forall t u, epstep t u -> rtc fstep t u.
Proof.
  intros t u H. apply (proj1 epstep_fsteps_mut t u H).
Qed.

Lemma cstep_fsteps_instance : forall t u, cstep t u -> rtc fstep t u.
Proof.
  intros t u H; destruct H as [t u Hp | t u He].
  - induction Hp as [t | t v u H IH].
    + apply rtc_refl.
    + eapply rtc_trans; [apply pstep_fsteps_instance; exact H | assumption].
  - induction He as [t | t v u H IH].
    + apply rtc_refl.
    + eapply rtc_trans; [apply epstep_fsteps_instance; exact H | assumption].
Qed.

Lemma rtc_fstep_cstep_instance : forall t u, rtc fstep t u -> rtc cstep t u.
Proof.
  intros t u H; induction H as [t | t v u H IH].
  - apply rtc_refl.
  - eapply rtc_step; [apply fstep_cstep; exact H | assumption].
Qed.

Lemma rtc_cstep_fsteps_instance : forall t u, rtc cstep t u -> rtc fstep t u.
Proof.
  intros t u H; induction H as [t | t v u H IH].
  - apply rtc_refl.
  - eapply rtc_trans; [apply cstep_fsteps_instance; exact H | assumption].
Qed.

Lemma fstep_confluent_instance : confluent fstep.
Proof.
  unfold confluent. intros x y z Hy Hz.
  destruct (cstep_confluent x y z
      (rtc_fstep_cstep_instance _ _ Hy)
      (rtc_fstep_cstep_instance _ _ Hz)) as [w [Hyw Hzw]].
  exists w. split;
    [ apply rtc_cstep_fsteps_instance; exact Hyw
    | apply rtc_cstep_fsteps_instance; exact Hzw ].
Qed.
End _luna_instance_core_paths.

(* Checked signature-transport component: _luna_instance_union. *)
Module _luna_instance_union.
Lemma rtc_R_single_S_commute : forall (A : Type) (R S : A -> A -> Prop),
  (forall x y z, R x y -> S x z -> exists w, S y w /\ rtc R z w) ->
  forall x y z, rtc R x y -> S x z ->
    exists w, S y w /\ rtc R z w.
Proof.
  intros A R S H x y z Hxy. revert z. induction Hxy as [x|x y' y Hxy Hyy' IH]; intros z Hz.
  - exists z. split; [exact Hz|apply rtc_refl].
  - destruct (H _ _ _ Hxy Hz) as [w [Hyw Hzw]].
    destruct (IH w Hyw) as [q [Hyq Hzq]].
    exists q. split; [exact Hyq|eapply rtc_trans; eassumption].
Qed.

Lemma rtc_R_S_commute : forall (A : Type) (R S : A -> A -> Prop),
  (forall x y z, R x y -> S x z -> exists w, S y w /\ rtc R z w) ->
  forall x y z, rtc R x y -> rtc S x z ->
    exists w, rtc S y w /\ rtc R z w.
Proof.
  intros A R S H x y z Hxy Hxz. revert Hxy. revert y.
  induction Hxz as [x|x z' z Hxz Hzz' IH]; intros y Hxy.
  - exists y. split; [apply rtc_refl|exact Hxy].
  - destruct (rtc_R_single_S_commute A R S H _ _ _ Hxy Hxz)
      as [q [Hyq Hzq]].
    destruct (IH q Hzq) as [w [Hqw Hzw]].
    exists w. split; [eapply rtc_trans; [apply rtc_one; exact Hyq|exact Hqw]|exact Hzw].
Qed.

Inductive block_union (A : Type) (R S : A -> A -> Prop) : A -> A -> Prop :=
| bu_left : forall x y, rtc R x y -> block_union A R S x y
| bu_right : forall x y, rtc S x y -> block_union A R S x y.

Lemma block_union_diamond : forall (A : Type) (R S : A -> A -> Prop),
  confluent R -> confluent S ->
  (forall x y z, R x y -> S x z -> exists w, S y w /\ rtc R z w) ->
  diamond (block_union A R S).
Proof.
  intros A R S HR HS Hcomm x y z Hxy Hxz.
  destruct Hxy as [x y Hxy|x y Hxy]; destruct Hxz as [x z Hxz|x z Hxz].
  - destruct (HR x y z Hxy Hxz) as [w [Hyw Hzw]].
    exists w; split; [apply bu_left|apply bu_left]; assumption.
  - destruct (rtc_R_S_commute A R S Hcomm _ _ _ Hxy Hxz)
      as [w [Hyw Hzw]].
    exists w; split; [apply bu_right|apply bu_left]; assumption.
  - destruct (rtc_R_S_commute A R S Hcomm _ _ _ Hxz Hxy)
      as [w [Hzw Hyw]].
    exists w; split; [apply bu_left|apply bu_right]; assumption.
  - destruct (HS x y z Hxy Hxz) as [w [Hyw Hzw]].
    exists w; split; [apply bu_right|apply bu_right]; assumption.
Qed.

Lemma block_union_confluent : forall (A : Type) (R S : A -> A -> Prop),
  confluent R -> confluent S ->
  (forall x y z, R x y -> S x z -> exists w, S y w /\ rtc R z w) ->
  confluent (block_union A R S).
Proof.
  intros; apply diamond_rtc_confluent, block_union_diamond; assumption.
Qed.
End _luna_instance_union.

(* Checked signature-transport component: _parent_instance_join. *)
Module _parent_instance_join.
Import _parent_instance_pruning _parent_pruning_diamond _parent_pruning_commute _luna_instance_core_paths _luna_instance_union _luna_instance_conversion.
Import TypeRulesCore.

Definition instance_reduce := block_union term fstep prune_term.
Definition instance_join t u := exists w, rtc instance_reduce t w /\ rtc instance_reduce u w.

Lemma instance_reduce_confluent : confluent instance_reduce.
Proof.
  apply block_union_confluent; [apply fstep_confluent_instance|
    apply prune_term_confluent|exact fstep_prune_commute].
Qed.
Lemma instance_join_refl : forall t, instance_join t t.
Proof. intro t; exists t; split; apply rtc_refl. Qed.
Lemma instance_join_sym : forall t u, instance_join t u -> instance_join u t.
Proof. intros t u [w [H1 H2]]; exists w; auto. Qed.
Lemma instance_join_trans : forall t u v,
  instance_join t u -> instance_join u v -> instance_join t v.
Proof.
  intros t u v [w [Htw Huw]] [z [Huz Hvz]].
  destruct (instance_reduce_confluent u w z Huw Huz) as [q [Hwq Hzq]].
  exists q; split; eapply rtc_trans; eassumption.
Qed.
Lemma fconv_instance_join : forall t u, fconv t u -> instance_join t u.
Proof.
  intros t u H; induction H.
  - exists u. split; [apply rtc_one, bu_left, rtc_one; exact H|apply rtc_refl].
  - apply instance_join_refl.
  - apply instance_join_sym; assumption.
  - eapply instance_join_trans; eassumption.
Qed.
Lemma instance_conv_join : forall t u, instance_conv t u -> instance_join t u.
Proof.
  intros t u H; induction H.
  - apply fconv_instance_join; assumption.
  - exists u. split; [apply rtc_one, bu_right, rtc_one; exact H|apply rtc_refl].
  - apply instance_join_refl.
  - apply instance_join_sym; assumption.
  - eapply instance_join_trans; eassumption.
Qed.
End _parent_instance_join.

(* Checked signature-transport component: _parent_instance_observations. *)
Module _parent_instance_observations.
Import SignatureConversion SignatureInstances _parent_instance_pruning _luna_instance_membership.
Import ListNotations TypeRulesCore _work_cjoin _work_cstep_invariants
 _work_conv_whd_pos _tmp_epstep _work_mixed_closure.

Lemma spine_mem_joined : forall c L, spine_mem c L ->
  joined_mem (phi_erase c) (phi_erase L).
Proof.
  intros c L H; induction H.
  - eapply jm_here with (A:=phi_erase A) (d:=phi_erase c') (R:=phi_erase Phi'); [exact (conv_phi_cjoin _ _ (conv_of_eval _ _ H))|].
    apply conv_phi_cjoin; exact H0.
  - eapply jm_there with (A:=phi_erase A) (d:=phi_erase c') (R:=phi_erase Phi'); [exact (conv_phi_cjoin _ _ (conv_of_eval _ _ H))|exact IHspine_mem].
Qed.

Lemma instance_erased_join : forall t,
 cjoin (phi_erase (instance_translate t)) (phi_erase t).
Proof.
  intro t. exists (phi_erase t). split; [apply rtc_one, cs_eta, rtc_one, instance_translate_erased_eta|apply rtc_refl].
Qed.

Lemma joined_tag_position : forall c n bs d,
 enum_pos c n -> Forall (fun d => exists m, enum_pos d m) bs ->
 In d bs -> cjoin (phi_erase c) (phi_erase d) -> enum_pos d n.
Proof.
  intros c n bs d Hc Hbs Hd Hcd.
  rewrite Forall_forall in Hbs. destruct (Hbs d Hd) as [m Hdm].
  pose proof (phi_erase_enum_pos _ _ Hc) as Hec.
  pose proof (phi_erase_enum_pos _ _ Hdm) as Hed.
  destruct Hcd as [w [Hcw Hdw]].
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hcw Hec) as Hwc.
  pose proof (rtc_cstep_enum_pos_id _ _ _ Hdw Hed) as Hwd.
  subst w. assert (Hmn : m = n).
  { eapply enum_pos_functional; [exact Hed|]. rewrite <- Hwd; exact Hec. }
  subst m; exact Hdm.
Qed.
End _parent_instance_observations.

(* Checked signature-transport component: _luna_instance_shape. *)
Module _luna_instance_shape.
Import SignatureInstances _parent_instance_pruning _parent_pruning_commute.
Import _tmp_epstep.
Import ListNotations TypeRulesCore.

Definition instance_luna (B L i : term) : term :=
  TApp (TMuS (TPair B L)) i.

Lemma fstep_instance_inv : forall B L i t,
    fstep (instance_luna B L i) t ->
    (exists B', t = instance_luna B' L i /\ fstep B B') \/
    (exists L', t = instance_luna B L' i /\ fstep L L') \/
    (exists i', t = instance_luna B L i' /\ fstep i i').
Proof.
  intros B L i t H. unfold instance_luna in *.
  inversion H; subst; eauto using fstep.
  all: try solve [inversion H0; subst; eauto using fstep].
  all: try match goal with
    Hf : fstep (TMuS (TPair _ _)) _ |- _ =>
      inversion Hf; subst; eauto using fstep
    end.
  all: try solve [inversion H0; subst; eauto using fstep].
  all: try solve [inversion H1; subst; eauto using fstep].
  all: try solve [inversion H2; subst; eauto using fstep].
  all: try match goal with
    Hx : fstep (TPair _ _) _ |- _ => inversion Hx; subst; eauto using fstep
    end.
  all: try match goal with
    Hx : fstep (TMuS _) _ |- _ => inversion Hx; subst; eauto using fstep
    end.
  all: try solve [inversion H0; subst; eauto using fstep, fs_app1, fs_app2].
  repeat match goal with
  | Hs : step (TApp (TMuS _) _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : step (TMuS _) _ |- _ => inversion Hs; subst; clear Hs
  | Hs : step (TPair _ _) _ |- _ => inversion Hs; subst; clear Hs
  | Hf : fstep (TMuS _) _ |- _ => inversion Hf; subst; clear Hf
  | Hf : fstep (TPair _ _) _ |- _ => inversion Hf; subst; clear Hf
  end;
  eauto 6 using fstep.
  all: match goal with
    Hx : fstep (TPair ?B ?L) ?S' |- _ =>
      destruct (pruning_fstep_pair_inv B L S' Hx)
        as [[Bnew [-> HB]] | [Lnew [-> HL]]];
      [ left; exists Bnew; auto | right; left; exists Lnew; auto ]
    end.
Qed.
Lemma prune_instance_inv : forall B L i t,
    prune_term (instance_luna B L i) t ->
    exists B' L' i', t = instance_luna B' L' i' /\
      prune_term B B' /\ prune_labels B L L' /\ prune_term i i'.
Proof.
  intros B L i t H. unfold instance_luna in *.
  inversion H; subst.
  all: try match goal with
    Hm : prune_term (TMuS (TPair ?B0 ?L0)) ?f' |- _ =>
      destruct (prune_mus_pair_inv B0 L0 f' Hm)
        as [B' [L' [-> [HB HL]]]];
      eexists; eexists; eexists; repeat split; eauto
    end.
  all: eexists; eexists; eexists; repeat split; eauto.
Qed.
End _luna_instance_shape.

(* Checked signature-transport component: _luna_instance_observer. *)
Module _luna_instance_observer.
Import SignatureInstances SignatureConversion _parent_instance_join _parent_instance_pruning _luna_instance_shape.
Import TypeRulesCore _tmp_epstep _work_cjoin.

Section Observer.
Variable B0 : term.
Variable O : term -> Prop.
Variable Hcore : forall L L', cjoin (phi_erase L) (phi_erase L') -> O L -> O L'.
Variable Hprune : forall B L L', cjoin (phi_erase B0) (phi_erase B) ->
  prune_labels B L L' -> O L -> O L'.

Definition instance_observation (t : term) : Prop :=
  exists B L i, t = signature_instance B L i /\
    cjoin (phi_erase B0) (phi_erase B) /\ O L.

Lemma fstep_observation : forall t u,
  fstep t u -> instance_observation t -> instance_observation u.
Proof.
  intros t u Hred [B [L [i [-> [HB HO]]]]].
  destruct (fstep_instance_inv B L i u Hred)
    as [[B' [-> H]] | [[L' [-> H]] | [i' [-> H]]]].
  - exists B', L, i. split; [reflexivity|]. split.
    + eapply cjoin_trans; [exact HB|apply conv_phi_cjoin; apply fstep_conv; exact H].
    + exact HO.
  - exists B, L', i. split; [reflexivity|]. split; [exact HB|].
    apply Hcore with (L := L) (L' := L');
      [apply conv_phi_cjoin; apply fstep_conv; exact H|exact HO].
  - exists B, L, i'. repeat split; assumption.
Qed.

Lemma prune_observation : forall t u,
  prune_term t u -> instance_observation t -> instance_observation u.
Proof.
  intros t u Hpr [B [L [i [-> [HB HO]]]]].
  destruct (prune_instance_inv B L i u Hpr) as [B' [L' [i' [-> [HPB [HPL HPI]]]]]].
  exists B', L', i'. split; [reflexivity|]. split.
  - rewrite (prune_erase _ _ HPB) in HB; exact HB.
  -
  apply Hprune with (B := B) (L := L) (L' := L'); assumption.
Qed.

Lemma instance_path_observation : forall t u,
  rtc instance_reduce t u -> instance_observation t -> instance_observation u.
Proof.
  assert (Hf : forall t u, rtc fstep t u ->
      instance_observation t -> instance_observation u).
  { intros t u Hr; induction Hr as [t|t v u Htv Hvu IH]; intros Ho.
    - exact Ho.
    - apply IH. exact (fstep_observation t v Htv Ho). }
  assert (Hp : forall t u, rtc prune_term t u ->
      instance_observation t -> instance_observation u).
  { intros t u Hr; induction Hr as [t|t v u Htv Hvu IH]; intros Ho.
    - exact Ho.
    - apply IH. exact (prune_observation t v Htv Ho). }
  intros t u Hr; induction Hr as [t|t v u Htv Hvu IH]; intros Ho.
  - exact Ho.
  - apply IH. destruct Htv as [t v Hfv|t v Hpv].
    + apply (Hf t v); assumption.
    + apply (Hp t v); assumption.
Qed.

End Observer.
End _luna_instance_observer.

(* Checked signature-transport component: _parent_signature_transport. *)
Module _parent_signature_transport.
Import SignatureInstances SignatureConversion SignatureProgressReduction _parent_instance_pruning _luna_instance_membership _luna_instance_coverage _parent_instance_translation _parent_instance_join _parent_instance_observations _luna_instance_observer _luna_instance_conversion.
Import ListNotations TypeRulesCore _tmp_epstep _work_cjoin
 _work_cstep_invariants.

Lemma translated_instances_join : forall S0 i0 S1 i1,
 conv (TApp (TMuS S0) i0) (TApp (TMuS S1) i1) ->
 instance_join
  (signature_instance (instance_translate (branches (TApp S0 i0)))
    (instance_translate (labels (TApp S0 i0))) (instance_translate i0))
  (signature_instance (instance_translate (branches (TApp S1 i1)))
    (instance_translate (labels (TApp S1 i1))) (instance_translate i1)).
Proof.
 intros S0 i0 S1 i1 HC. apply instance_conv_join.
 eapply ic_trans.
 - apply ic_sym, ic_core, fc_step, fs_step, instance_translate_musapp.
 - eapply ic_trans; [apply instance_translate_conv_parent; exact HC|].
   apply ic_core, fc_step, fs_step, instance_translate_musapp.
Qed.

Lemma conv_fconv_nophi : forall t u, conv t u -> fconv t u.
Proof.
  intros t u H; induction H; eauto using fconv, fstep.
  all: try (eapply fconv_map; eauto using fstep).
  all: try (eapply fconv_map2; eauto using fstep).
  all: try (eapply fconv_map3; eauto using fstep).
  all: try (eapply fconv_map4; eauto using fstep).
  all: try (eapply fconv_map5; eauto using fstep).
  all: try (apply fc_step, fs_eta).
  - eapply (fconv_map2 (fun x y => TCase x y bs)); eauto using fstep.
  - eapply (fconv_map2
      (fun x y => TCase M Q (bs1 ++ (x,y) :: bs2)));
      eauto using fstep.
Qed.

Lemma cjoin_pair_snd_nophi : forall a b a' b',
  cjoin (TPair a b) (TPair a' b') -> cjoin b b'.
Proof.
  intros a b a' b' Hpair.
  assert (Hsnd : cjoin (TSnd (TPair a b)) (TSnd (TPair a' b'))).
  { eapply cjoin_map_parent.
    - intros; apply ps_snd; assumption.
    - intros; apply eps_snd; assumption.
    - exact Hpair. }
  assert (HL : rtc _work_mixed_closure.cstep (TSnd (TPair a b)) b).
  { apply rtc_one, _work_mixed_closure.pstep_cstep, step_pstep, st_snd. }
  assert (HR : rtc _work_mixed_closure.cstep (TSnd (TPair a' b')) b').
  { apply rtc_one, _work_mixed_closure.pstep_cstep, step_pstep, st_snd. }
  eapply cjoin_reduce_right; [eapply cjoin_reduce_left; eassumption | exact HR].
Qed.

Lemma packed_mus_labels_conv : forall E0 S0 i0 E1 S1 i1,
  conv (TApp (SigMu E0 S0) i0) (TApp (SigMu E1 S1) i1) ->
  conv (labels (TApp S0 i0)) (labels (TApp S1 i1)).
Proof.
  intros E0 S0 i0 E1 S1 i1 HC.
  destruct (cjoin_musapp_inv_luna _ _ _ _
    (fconv_cjoin _ _ (conv_fconv_nophi _ _ HC))) as [Hpair Hi].
  pose proof (cjoin_pair_snd_nophi _ _ _ _ Hpair) as HS.
  unfold labels. apply cjoin_conv_bridge.
  eapply cjoin_map_parent.
  - intros; apply ps_snd; assumption.
  - intros; apply eps_snd; assumption.
  - apply cjoin_app_parent; assumption.
Qed.

Lemma joined_mem_label_transport : forall c d L,
  cjoin c d -> joined_mem c L -> joined_mem d L.
Proof.
  intros c d L Hcd Hm; induction Hm.
  - eapply jm_here; [exact H|].
    eapply cjoin_trans; [apply cjoin_sym; exact Hcd|exact H0].
  - eapply jm_there; eassumption.
Qed.

Lemma joined_mem_spine_tail : forall c Phi Psi,
  joined_mem (phi_erase c) (phi_erase Phi) -> spine_tail Phi Psi ->
  joined_mem (phi_erase c) (phi_erase Psi).
Proof.
  intros c Phi Psi Hm Ht; induction Ht.
  - eapply joined_mem_transport; [exact Hm|].
    apply cjoin_sym, conv_phi_cjoin, conv_of_eval; exact H.
  - apply jm_there with (A:=phi_erase A) (d:=phi_erase c0)
      (R:=phi_erase Psi').
    + change (cjoin (phi_erase Psi) (phi_erase (TLCons A c0 Psi'))).
      apply conv_phi_cjoin, conv_of_eval; exact H.
    + apply IHHt; exact Hm.
Qed.

Lemma joined_mem_spine_incl : forall c Phi Psi,
  joined_mem (phi_erase c) (phi_erase Phi) -> spine_incl Phi Psi ->
  joined_mem (phi_erase c) (phi_erase Psi).
Proof.
  intros c Phi Psi Hm Hi; revert c Hm.
  induction Hi; intros x Hm.
  - exfalso. apply (joined_mem_nil_absurd (phi_erase x) (phi_erase A)).
    eapply joined_mem_transport; [exact Hm|].
    change (cjoin (phi_erase Phi) (phi_erase (TLNil A))).
    apply conv_phi_cjoin, conv_of_eval; exact H.
  - assert (Hmcons : joined_mem (phi_erase x)
        (phi_erase (TLCons A c Phi'))).
    { eapply joined_mem_transport; [exact Hm|].
      change (cjoin (phi_erase Phi) (phi_erase (TLCons A c Phi'))).
      apply conv_phi_cjoin, conv_of_eval; exact H. }
    destruct (joined_mem_cons_inv _ _ _ _ Hmcons) as [Hxc|Htail].
    + eapply joined_mem_label_transport.
      * apply cjoin_sym; exact Hxc.
      * apply spine_mem_joined; exact H0.
    + apply IHHi. exact Htail.
  - eapply joined_mem_spine_tail; eassumption.
Qed.

Lemma sub_packed_mus_source : forall G X Y, sub G X Y ->
  forall E S i, conv Y (TApp (SigMu E S) i) ->
  exists E0 S0 i0, conv X (TApp (SigMu E0 S0) i0).
Proof.
  intros G X Y HS; induction HS; intros E0 S0 i0 HY.
  - exists E0,S0,i0. eapply cv_trans; eassumption.
  - destruct (IHHS2 E0 S0 i0 HY) as [E1 [S1 [i1 HM]]].
    exact (IHHS1 E1 S1 i1 HM).
  - exfalso. pose proof (conv_whd _ _ _ _ HY
      (whd_shape _ HSort (hs_sort k))
      (whd_shape _ HMuSApp (hs_musapp (TPair E0 S0) i0))) as K.
    discriminate.
  - exfalso. pose proof (conv_whd _ _ _ _ HY
      (whd_shape _ HPi (hs_pi A' B'))
      (whd_shape _ HMuSApp (hs_musapp (TPair E0 S0) i0))) as K.
    discriminate.
  - exfalso.
    assert (HW : whd (TApp (Carrier E Sf) i) HMuIApp).
    { unfold Carrier. apply whd_shape. constructor. }
    pose proof (conv_whd _ _ _ _ HY HW
      (whd_shape _ HMuSApp (hs_musapp (TPair E0 S0) i0))) as K.
    discriminate.
  - exists E,S1,i. apply cv_refl.
Qed.

Lemma sub_packed_mus_joined_mem : forall G X Y,
  sub G X Y -> forall E0 S0 i0 E1 S1 i1 c,
  conv X (TApp (SigMu E0 S0) i0) ->
  conv Y (TApp (SigMu E1 S1) i1) ->
  joined_mem (phi_erase c) (phi_erase (labels (TApp S0 i0))) ->
  joined_mem (phi_erase c) (phi_erase (labels (TApp S1 i1))).
Proof.
  intros G X Y HS; induction HS; intros E0 S0 i0 Ex Sx ix c HX HY HM.
  - eapply joined_mem_transport; [exact HM|].
    apply conv_phi_cjoin.
    eapply packed_mus_labels_conv with (E0:=E0) (E1:=Ex).
    eapply cv_trans; [apply cv_sym; exact HX|].
    eapply cv_trans; [exact H|exact HY].
  - destruct (sub_packed_mus_source _ _ _ HS2 Ex Sx ix HY)
      as [Em [Sm [im HMID]]].
    apply (IHHS2 Em Sm im Ex Sx ix c HMID HY).
    apply (IHHS1 E0 S0 i0 Em Sm im c HX HMID HM).
  - exfalso. pose proof (conv_whd _ _ _ _ HY
      (whd_shape _ HSort (hs_sort k))
      (whd_shape _ HMuSApp (hs_musapp (TPair Ex Sx) ix))) as K.
    discriminate.
  - exfalso. pose proof (conv_whd _ _ _ _ HY
      (whd_shape _ HPi (hs_pi A' B'))
      (whd_shape _ HMuSApp (hs_musapp (TPair Ex Sx) ix))) as K.
    discriminate.
  - exfalso.
    assert (HW : whd (TApp (Carrier E Sf) i) HMuIApp).
    { unfold Carrier. apply whd_shape. constructor. }
    pose proof (conv_whd _ _ _ _ HY HW
      (whd_shape _ HMuSApp (hs_musapp (TPair Ex Sx) ix))) as K.
    discriminate.
  - pose proof (packed_mus_labels_conv _ _ _ _ _ _ HX) as HLX.
    pose proof (packed_mus_labels_conv _ _ _ _ _ _ HY) as HLY.
    assert (HM0 : joined_mem (phi_erase c)
      (phi_erase (labels (TApp S1 i)))).
    { eapply joined_mem_transport; [exact HM|].
      apply cjoin_sym, conv_phi_cjoin; exact HLX. }
    assert (HM1 : joined_mem (phi_erase c) (phi_erase Phi1)).
    { eapply joined_mem_transport; [exact HM0|].
      apply conv_phi_cjoin, conv_of_eval; exact H4. }
    assert (HM2 : joined_mem (phi_erase c) (phi_erase Phi2)).
    { eapply joined_mem_spine_incl; [exact HM1|exact H6]. }
    assert (HM3 : joined_mem (phi_erase c)
      (phi_erase (labels (TApp S2 i)))).
    { eapply joined_mem_transport; [exact HM2|].
      apply cjoin_sym, conv_phi_cjoin, conv_of_eval; exact H5. }
    eapply joined_mem_transport; [exact HM3|].
    apply conv_phi_cjoin; exact HLY.
Qed.

Lemma signature_tag_transport_proved : signature_tag_transport.
Proof.
  intros N E0 S0 i0 E1 S1 i1 c n xs X bs
    HP Hsz Hxs Hsub Hpos Hbs Hmem Hcov.
  assert (HM0 : joined_mem (phi_erase c)
      (phi_erase (labels (TApp S0 i0)))).
  { apply spine_mem_joined; exact Hmem. }
  assert (HM1 : joined_mem (phi_erase c)
      (phi_erase (labels (TApp S1 i1)))).
  { eapply sub_packed_mus_joined_mem with
      (X:=TApp (SigMu E0 S0) i0) (Y:=TApp (SigMu E1 S1) i1)
      (E0:=E0) (S0:=S0) (i0:=i0) (E1:=E1) (S1:=S1) (i1:=i1).
    - exact Hsub.
    - apply cv_refl.
    - apply cv_refl.
    - exact HM0. }
  destruct (joined_mem_covered _ _ _ HM1 (covers_joined _ _ Hcov))
    as [d [Hd Hcd]].
  left. exists d. split; [exact Hd|].
  eapply joined_tag_position; eassumption.
Qed.
Theorem progress_without_signature_axiom : forall t A, check [] t A ->
 value t \/ exists t', step t t'.
Proof. apply progress_from_signature_tag_transport, signature_tag_transport_proved. Qed.
End _parent_signature_transport.

Lemma progress_n : forall N,
    (forall t A, tsize t <= N -> check [] t A ->
       value t \/ exists t', step t t') /\
    (forall c T, tsize c <= N -> check [] c T -> whd T HEnumT ->
       (exists m, enum_pos c m) \/ exists c', step c c').
Proof.
  exact (SignatureProgressReduction.progress_n_transport
    _parent_signature_transport.signature_tag_transport_proved).
Qed.

Theorem progress_proved : forall t A,
    check [] t A -> value t \/ exists t', step t t'.
Proof.
  intros t A Hck.
  destruct (progress_n (tsize t)) as [Hmain _].
  exact (Hmain t A (le_n (tsize t)) Hck).
Qed.

Print Assumptions progress_proved.

(* Public name formerly declared as a conjecture in TypeRules.v. *)
Theorem progress : forall t A,
    check [] t A -> value t \/ exists t', step t t'.
Proof. exact progress_proved. Qed.

Print Assumptions progress.
