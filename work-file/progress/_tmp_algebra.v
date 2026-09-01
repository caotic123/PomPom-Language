Require Import TypeRules Progress.
From Stdlib Require Import List Arith Lia.
Import ListNotations.

Lemma subst_lift_offset_var_test : forall n u e i j, i <= j ->
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

Lemma subst_subst_comm_var_test : forall n u a k j,
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
    replace (j+k) with (j+k) by reflexivity.
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

Lemma subst_lift_offset_test : forall t u e i j, i <= j ->
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
  all: try solve [apply subst_lift_offset_var_test; exact Hij].
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

Lemma subst_subst_comm_test : forall t u a k j,
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
  all: try solve [apply subst_subst_comm_var_test].
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
