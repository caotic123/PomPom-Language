(* ========================================================================== *)
(*  Progress.v — a proof of TypeRules.v's progress conjecture, RELATIVE to a  *)
(*  small, explicitly named interface of confluence-grade facts about the     *)
(*  untyped conversion (the §10 obligations this file does NOT discharge).    *)
(*                                                                            *)
(*  Theorem progress_proved at the end has the exact statement of the         *)
(*  progress conjecture; Print Assumptions lists what it stands on:           *)
(*    conv_whd, conv_enumt_inj, conv_pos, spine_covered, muapp_sort           *)
(*    (this file's interface), and canonical_forms_sig (TypeRules §8).        *)
(*  Everything else — canonical forms, typing inversion, the first-match     *)
(*  selection argument — is proved.                                           *)
(* ========================================================================== *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import TypeRules.

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
  intros R i A Hv Hs. inversion Hs; subst. inversion H1; subst.
  pose proof (eval_pi_sort _ _ H3 _ _ _ eq_refl eq_refl) as HB.
  rewrite HB. subst. cbn. reflexivity.
Qed.

Lemma mus_app_synth_sort : forall Sf i A,
    value (TApp (TMuS Sf) i) ->
    synth [] (TApp (TMuS Sf) i) A -> A = TSort 0.
Proof.
  intros Sf i A Hv Hs. inversion Hs; subst. inversion H1; subst.
  pose proof (eval_pi_sort _ _ H3 _ _ _ eq_refl eq_refl) as HB.
  rewrite HB. subst. cbn. reflexivity.
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
  - exists A. split; [apply ao_syn; exact H | exact H0].
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
    match goal with Hr : pstep (TypeRules.TPair _ _) _ |- _ =>
      inversion Hr; clear Hr; subst
    end.
    cbn in H. inversion H; subst.
    eapply ps_fst_pair; eauto.
  - destruct p; cbn;
      try solve [eapply ps_snd; eauto].
    match goal with Hr : pstep (TypeRules.TPair _ _) _ |- _ =>
      inversion Hr; clear Hr; subst
    end.
    cbn in H. inversion H; subst.
    eapply ps_snd_pair; eauto.
  - destruct E; cbn;
      try solve [eapply ps_epi; eauto].
    + match goal with Hr : pstep TypeRules.TNilE _ |- _ =>
        inversion Hr; clear Hr; subst
      end.
      eapply ps_epi_nil; eauto.
    + match goal with Hr : pstep (TypeRules.TConsE _ _) _ |- _ =>
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
      Hcpos : TypeRules.enum_pos ?cc ?nn,
      Hapos : TypeRules.enum_pos ?aa ?nn |- _ =>
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

(* ------------------------------------------------------------------ *)
(*  THE ASSUMPTION INTERFACE — confluence-grade facts about conv       *)
(*  (the §10 conversion metatheory), stated as narrowly as the proof   *)
(*  needs.  Each is a consequence of confluence-modulo-eta/phi of the  *)
(*  raw reduction; none is proved here.                                *)
(* ------------------------------------------------------------------ *)

(* conversion cannot cross weak-head classes (λ is unclassified, so eta
   never witnesses a crossing; cv_phi stays inside HMuSApp) *)
Conjecture conv_whd : forall t u h1 h2,
    conv t u -> whd t h1 -> whd u h2 -> h1 = h2.

(* EnumT is injective up to conversion *)
Conjecture conv_enumt_inj : forall E1 E2,
    conv (TEnumT E1) (TEnumT E2) -> conv E1 E2.

(* conversion-related canonical positions are the same position *)
Conjecture conv_pos : forall c d n m,
    conv c d -> enum_pos c n -> enum_pos d m -> n = m.

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

(* a stuck μ-application value classifies only as a sort: its type is
   Set₀ up to conversion (Π-injectivity + substitution-compatibility) *)
Conjecture muapp_sort : forall f a T U h,
    check [] (TApp f a) T -> value (TApp f a) ->
    conv T U -> whd U h -> h = HSort.

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
    | Hs : synth [] ?t0 ?A0, Hsub : sub [] ?A0 ?B0 |- _ =>
        destruct (sub_transport [] A0 B0 Hsub U h Hc Hw) as
          [HcAU | [[Hh [U' [HcU' Hw']]] | [Heq [U' [HcU' Hw']]]]];
        [ eapply canon_syn; [exact Hs | exact Hval | exact HcAU | exact Hw]
        | destruct Hh as [-> | [-> | ->]];
          (assert (K : canon _ _ U') by
             (eapply canon_syn; [exact Hs | exact Hval | exact HcU' | exact Hw']);
           exact K)
        | subst h; destruct Hw' as [Hw' | Hw'];
          [ assert (K : canon _ HMuIApp U') by
              (eapply canon_syn; [exact Hs | exact Hval | exact HcU' | exact Hw']);
            exact K
          | assert (K : canon _ HMuSApp U') by
              (eapply canon_syn; [exact Hs | exact Hval | exact HcU' | exact Hw']);
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
  - match goal with Hs : synth [] (TVar _) _ |- _ =>
      inversion Hs; subst;
      match goal with Hne : nth_error [] ?m = Some _ |- _ =>
        destruct m; discriminate Hne end
    end.
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
  - syn_app_emit.
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
  - syn_proj_emit.
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
  - syn_proj_emit.
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
  - syn_prem_emit.
  - exact (IHHck eq_refl E0 P0 eq_refl).
Qed.

Lemma inv_switch : forall G t T, check G t T -> G = [] ->
    forall E P p e, t = TSwitch E P p e ->
    check [] E TEnumU /\ check [] p (TEPi E P) /\ check [] e (TEnumT E).
Proof.
  intros G t T Hck. induction Hck; intros HG E0 P0 p0 e0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl E0 P0 p0 e0 eq_refl).
Qed.

Lemma inv_interp : forall G t T, check G t T -> G = [] ->
    forall D X, t = TInterp D X -> exists IT, check [] D (TIDesc IT).
Proof.
  intros G t T Hck. induction Hck; intros HG D0 X0 Heq; subst; try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl D0 X0 eq_refl).
Qed.

Lemma inv_iall : forall G t T, check G t T -> G = [] ->
    forall D X xs P, t = TIAll D X xs P ->
    (exists IT, check [] D (TIDesc IT)) /\ check [] xs (TInterp D X).
Proof.
  intros G t T Hck. induction Hck; intros HG D0 X0 xs0 P0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl D0 X0 xs0 P0 eq_refl).
Qed.

Lemma inv_hyps : forall G t T, check G t T -> G = [] ->
    forall D X P h xs, t = THyps D X P h xs ->
    (exists IT, check [] D (TIDesc IT)) /\ check [] xs (TInterp D X).
Proof.
  intros G t T Hck. induction Hck; intros HG D0 X0 P0 h0 xs0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl D0 X0 P0 h0 xs0 eq_refl).
Qed.

Lemma inv_ind : forall G t T, check G t T -> G = [] ->
    forall R P stp i x, t = TInd R P stp i x ->
    check [] x (TApp (TMuI R) i).
Proof.
  intros G t T Hck. induction Hck; intros HG R0 P0 stp0 i0 x0 Heq; subst;
    try discriminate.
  - syn_prem_emit.
  - syn_prem_emit.
  - exact (IHHck eq_refl R0 P0 stp0 i0 x0 eq_refl).
Qed.

Lemma inv_case : forall G t T, check G t T -> G = [] ->
    forall M Q bs, t = TCase M Q bs ->
    exists Sf i IT E Phi,
      check [] M (TApp (TMuS Sf) i) /\
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
  - match goal with Hs : synth [] (TCase _ _ _) _ |- _ =>
      inversion Hs; subst;
      do 5 eexists; repeat split; eassumption
    end.
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

Lemma progress_n : forall N,
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
        apply conv_enumt_inj in Hcvt.
        assert (Hd : HConsE = HNilE).
        { eapply conv_whd;
            [exact Hcvt | apply whd_shape; constructor
            | apply whd_shape; constructor]. }
        discriminate Hd.
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
                    (whd_shape _ _ (hs_musapp Sf i))) as K.
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
      destruct (@canonical_forms_sig (TIn (TPair c xs)) Sf i IT E
                  HIT HE HSf Hi HM)
        as (c1 & xs1 & Phi1 & HevM & HevL & Hmem1 & _).
      destruct (eval_in_tag n c xs _ Hn HevM) as [xs' Heq1].
      inversion Heq1; subst.
      assert (HmemL : spine_mem c (labels (TApp Sf i))).
      { eapply spine_mem_pre; [exact HevL | exact Hmem1]. }
      assert (HcovL : covers (map fst bs) (labels (TApp Sf i))).
      { eapply covers_pre; [exact Hlab | exact Hcov]. }
      destruct (spine_covered _ _ _ HmemL HcovL) as [d [Hind Hcvd]].
      apply in_map_iff in Hind. destruct Hind as [[d0 bd] [Hfst Hinbs]].
      cbn in Hfst. subst d0.
      destruct (forall2_in_l _ _ _ _ _ _ Hns Hinbs) as [m [Hinm Hpm]].
      cbn in Hpm.
      assert (Hmn : n = m) by
        (eapply conv_pos; [exact Hcvd | exact Hn | exact Hpm]).
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

Theorem progress_proved : forall t A,
    check [] t A -> value t \/ exists t', step t t'.
Proof.
  intros t A Hck.
  destruct (progress_n (tsize t)) as [Hmain _].
  exact (Hmain t A (le_n (tsize t)) Hck).
Qed.

Print Assumptions progress_proved.
