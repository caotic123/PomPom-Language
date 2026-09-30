Require Import Progress.
From Stdlib Require Import List Arith Lia.
Import ListNotations.
Open Scope string_scope.

Lemma test_lift_lift_add_var : forall n d e k,
    TypeRules.lift d k (TypeRules.lift e k (TypeRules.TVar n)) =
    TypeRules.lift (d+e) k (TypeRules.TVar n).
Proof.
  intros n d e k. cbn [TypeRules.lift].
  destruct (Nat.ltb n k) eqn:Hnk.
  - cbn [TypeRules.lift]. rewrite Hnk. reflexivity.
  -
    rewrite Nat.ltb_ge in Hnk.
    cbn [TypeRules.lift].
    assert (Hnk' : Nat.ltb (e+n) k = false) by
      (apply Nat.ltb_ge; lia).
    rewrite Hnk'.
    f_equal; lia.
Qed.

Lemma test_subst_lift_gen_var : forall n u j k i,
    TypeRules.subst u (j+k+i) (TypeRules.lift j i (TypeRules.TVar n)) =
    TypeRules.lift j i (TypeRules.subst u (k+i) (TypeRules.TVar n)).
Proof.
  intros n u j k i.
  destruct (Nat.ltb n i) eqn:Hni.
  - apply Nat.ltb_lt in Hni.
    assert (Hnki : Nat.ltb n (k+i) = true) by (apply Nat.ltb_lt; lia).
    assert (Hnjki : Nat.ltb n (j+k+i) = true) by (apply Nat.ltb_lt; lia).
    assert (Hn0 : Nat.ltb n i = true) by (apply Nat.ltb_lt; exact Hni).
    cbn [TypeRules.lift TypeRules.subst]. rewrite Hn0.
    cbn [TypeRules.lift TypeRules.subst]. rewrite Hnjki, Hnki.
    cbn [TypeRules.lift]. rewrite Hn0. reflexivity.
  - apply Nat.ltb_ge in Hni.
    destruct (Nat.lt_trichotomy n (k+i)) as [Hlt|[Heq|Hgt]].
    + assert (Hnki : Nat.ltb n (k+i) = true) by (apply Nat.ltb_lt; exact Hlt).
      assert (Hnjki : Nat.ltb (j+n) (j+k+i) = true) by (apply Nat.ltb_lt; lia).
      assert (Hni' : Nat.ltb n i = false) by (apply Nat.ltb_ge; exact Hni).
      cbn [TypeRules.lift TypeRules.subst]. rewrite Hni'.
      cbn [TypeRules.lift TypeRules.subst]. rewrite Hnjki, Hnki.
      cbn [TypeRules.lift]. rewrite Hni'. reflexivity.
    + subst n.
      assert (Hni' : Nat.ltb (k+i) i = false) by (apply Nat.ltb_ge; lia).
      assert (Hki : Nat.ltb (k+i) (k+i) = false) by (apply Nat.ltb_ge; lia).
      assert (Hjki : Nat.ltb (j+k+i) (j+k+i) = false) by (apply Nat.ltb_ge; lia).
      assert (Hejki : Nat.eqb (j+k+i) (j+k+i) = true) by (apply Nat.eqb_eq; reflexivity).
      assert (Heki : Nat.eqb (k+i) (k+i) = true) by (apply Nat.eqb_eq; reflexivity).
      cbn [TypeRules.lift TypeRules.subst]. rewrite Hni'.
      cbn [TypeRules.lift TypeRules.subst].
      replace (j+(k+i)) with (j+k+i) by lia.
      rewrite Hjki, Hejki, Hki, Heki.
      symmetry. apply test_lift_shift; lia.
    + assert (Hnki : Nat.ltb n (k+i) = false) by (apply Nat.ltb_ge; lia).
      assert (Hneki : Nat.eqb n (k+i) = false) by (apply Nat.eqb_neq; lia).
      assert (Hnjki : Nat.ltb (j+n) (j+k+i) = false) by (apply Nat.ltb_ge; lia).
      assert (Hjneki : Nat.eqb (j+n) (j+k+i) = false) by (apply Nat.eqb_neq; lia).
      assert (Hni' : Nat.ltb n i = false) by (apply Nat.ltb_ge; exact Hni).
      destruct n as [|q]; [lia|].
      cbn [TypeRules.lift TypeRules.subst]. rewrite Hni'.
      cbn [TypeRules.lift TypeRules.subst]. rewrite Hnjki, Hjneki, Hnki, Hneki.
      cbn [TypeRules.lift TypeRules.subst].
      f_equal. lia.
Qed.

Lemma test_lift_shift_var : forall n j i e q, i <= e ->
    TypeRules.lift j (i+q) (TypeRules.lift e q (TypeRules.TVar n)) =
    TypeRules.lift (j+e) q (TypeRules.TVar n).
Proof.
  intros n j i e q Hie.
  destruct (Nat.ltb n q) eqn:Hnq.
  - assert (Hnq' : Nat.ltb n q = true) by exact Hnq.
    apply Nat.ltb_lt in Hnq.
    assert (Hout : Nat.ltb n (i+q) = true) by (apply Nat.ltb_lt; lia).
    cbn [TypeRules.lift]. rewrite Hnq'.
    cbn [TypeRules.lift]. rewrite Hout. reflexivity.
  - assert (Hnq' : Nat.ltb n q = false) by exact Hnq.
    apply Nat.ltb_ge in Hnq.
    assert (Hen : Nat.ltb (e+n) (i+q) = false) by (apply Nat.ltb_ge; lia).
    cbn [TypeRules.lift]. rewrite Hnq'.
    cbn [TypeRules.lift]. rewrite Hen.
    cbn [TypeRules.lift].
    f_equal; lia.
Qed.

Lemma test_map_lift_shift : forall bs j i e q,
    i <= e ->
    (forall c b, In (c,b) bs ->
      TypeRules.lift j (i+q) (TypeRules.lift e q c) =
        TypeRules.lift (j+e) q c) ->
    (forall c b, In (c,b) bs ->
      TypeRules.lift j (S i+q) (TypeRules.lift e (S q) b) =
        TypeRules.lift (j+e) (S q) b) ->
    map (fun '(c,b) => (TypeRules.lift j (i+q) c,
                        TypeRules.lift j (S i+q) b))
      (map (fun '(c,b) => (TypeRules.lift e q c,
                           TypeRules.lift e (S q) b)) bs) =
    map (fun '(c,b) => (TypeRules.lift (j+e) q c,
                        TypeRules.lift (j+e) (S q) b)) bs.
Proof.
  intros bs j i e q Hie Hc Hb.
  induction bs as [|[c b] bs IH]; cbn; [reflexivity|].
  f_equal.
  - f_equal; [exact (Hc c b (or_introl eq_refl))
             | exact (Hb c b (or_introl eq_refl))].
  - apply IH; [intros c' b' Hin; exact (Hc c' b' (or_intror Hin))
              | intros c' b' Hin; exact (Hb c' b' (or_intror Hin))].
Qed.

Lemma test_lift_shift : forall t j i e q, i <= e ->
    TypeRules.lift j (i+q) (TypeRules.lift e q t) =
    TypeRules.lift (j+e) q t.
Proof.
  apply (tsize_strong_ind (fun t => forall j i e q, i <= e ->
    TypeRules.lift j (i+q) (TypeRules.lift e q t) =
      TypeRules.lift (j+e) q t)).
  intros t IH j i e q Hie. destruct t; cbn.
  all: try reflexivity.
  all: try solve [f_equal; apply IH; cbn; lia].
  all: try solve [replace (S (i+q)) with (i+S q) by lia;
    f_equal; apply IH; cbn; lia].
  - apply test_lift_shift_var; exact Hie.
  - f_equal.
    + apply (IH t1); cbn; lia.
    + apply (IH t2); cbn; lia.
    + apply test_map_lift_shift; [exact Hie| |].
      * intros c b Hin. apply (IH c).
        (* size premise *)
        eapply tsize_case_bs; exact Hin.
        (* cutoff premise *)
        exact Hie.
      * intros c b Hin. replace (S i+q) with (i+S q) by lia. apply (IH b).
        (* size premise *)
        eapply tsize_case_bs_body; exact Hin.
        (* cutoff premise *)
        exact Hie.
Qed.

Lemma test_map_lift_lift_add : forall bs d e k,
    (forall c b, In (c,b) bs ->
      TypeRules.lift d k (TypeRules.lift e k c) =
        TypeRules.lift (d+e) k c) ->
    (forall c b, In (c,b) bs ->
      TypeRules.lift d (S k) (TypeRules.lift e (S k) b) =
        TypeRules.lift (d+e) (S k) b) ->
    map (fun '(c,b) => (TypeRules.lift d k c,
                        TypeRules.lift d (S k) b))
      (map (fun '(c,b) => (TypeRules.lift e k c,
                           TypeRules.lift e (S k) b)) bs) =
    map (fun '(c,b) => (TypeRules.lift (d+e) k c,
                        TypeRules.lift (d+e) (S k) b)) bs.
Proof.
  intros bs d e k Hc Hb.
  induction bs as [|[c b] bs IH]; cbn; [reflexivity|].
  f_equal.
  - f_equal; [exact (Hc c b (or_introl eq_refl))
             | exact (Hb c b (or_introl eq_refl))].
  - apply IH; [intros c' b' Hin; exact (Hc c' b' (or_intror Hin))
              | intros c' b' Hin; exact (Hb c' b' (or_intror Hin))].
Qed.

Lemma test_lift_lift_add : forall t d e k,
    TypeRules.lift d k (TypeRules.lift e k t) =
    TypeRules.lift (d+e) k t.
Proof.
  apply (tsize_strong_ind (fun t => forall d e k,
    TypeRules.lift d k (TypeRules.lift e k t) =
    TypeRules.lift (d+e) k t)).
  intros t IH d e k. destruct t; cbn.
  all: try reflexivity.
  all: try solve [f_equal; apply IH; cbn; lia].
  all: try solve [repeat f_equal; apply IH; cbn; lia].
  - apply test_lift_lift_add_var.
  - f_equal.
    all: try (apply IH; cbn; lia).
    apply test_map_lift_lift_add.
    + intros c b0 Hin. apply (IH c); eapply tsize_case_bs; exact Hin.
    + intros c b0 Hin. apply (IH b0); eapply tsize_case_bs_body; exact Hin.
Qed.

Lemma test_subst_lift0_var : forall n u j k,
    TypeRules.subst u (j+k) (TypeRules.lift j 0 (TypeRules.TVar n)) =
    TypeRules.lift j 0 (TypeRules.subst u k (TypeRules.TVar n)).
Proof.
  intros n u j k.
  destruct (Nat.lt_trichotomy n k) as [Hlt|[Heq|Hgt]].
  - assert (Hnk : Nat.ltb n k = true) by (apply Nat.ltb_lt; exact Hlt).
    assert (Hn0 : Nat.ltb n 0 = false) by (apply Nat.ltb_ge; lia).
    assert (Hjnk : Nat.ltb (j+n) (j+k) = true) by
      (apply Nat.ltb_lt; lia).
    cbn [TypeRules.lift TypeRules.subst]. rewrite Hn0.
    cbn [TypeRules.lift TypeRules.subst].
    rewrite Hnk, Hjnk. reflexivity.
  - subst n.
    assert (Hn0 : Nat.ltb k 0 = false) by (apply Nat.ltb_ge; lia).
    assert (Hnk : Nat.ltb k k = false) by (apply Nat.ltb_ge; lia).
    assert (Hke : Nat.eqb k k = true) by (apply Nat.eqb_eq; reflexivity).
    assert (Hjnk : Nat.ltb (j+k) (j+k) = false) by (apply Nat.ltb_ge; lia).
    assert (Hjne : Nat.eqb (j+k) (j+k) = true) by (apply Nat.eqb_eq; reflexivity).
    cbn [TypeRules.lift TypeRules.subst]. rewrite Hn0.
    cbn [TypeRules.lift TypeRules.subst].
    rewrite Hnk, Hke, Hjnk, Hjne.
    symmetry. apply test_lift_lift_add.
  - destruct n as [|q]; [lia|].
    assert (Hn0 : Nat.ltb (S q) 0 = false) by (apply Nat.ltb_ge; lia).
    assert (Hnk : Nat.ltb (S q) k = false) by (apply Nat.ltb_ge; lia).
    assert (Hne : Nat.eqb (S q) k = false) by (apply Nat.eqb_neq; lia).
    assert (Hjnk : Nat.ltb (j+S q) (j+k) = false) by (apply Nat.ltb_ge; lia).
    assert (Hjne : Nat.eqb (j+S q) (j+k) = false) by (apply Nat.eqb_neq; lia).
    cbn [TypeRules.lift TypeRules.subst]. rewrite Hn0.
    cbn [TypeRules.lift TypeRules.subst].
    rewrite Hnk, Hne, Hjnk, Hjne.
    rewrite Nat.pred_succ.
    cbn [TypeRules.lift].
    assert (Hq0 : Nat.ltb q 0 = false) by (apply Nat.ltb_ge; lia).
    rewrite Hq0.
    f_equal; lia.
Qed.

Lemma test_subst_lift0 : forall t u j k,
    TypeRules.subst u (j+k) (TypeRules.lift j 0 t) =
    TypeRules.lift j 0 (TypeRules.subst u k t).
Proof.
  apply (tsize_strong_ind (fun t => forall u j k,
    TypeRules.subst u (j+k) (TypeRules.lift j 0 t) =
    TypeRules.lift j 0 (TypeRules.subst u k t))).
  intros t IH u j k. destruct t; cbn.
  all: try reflexivity.
  all: try solve [f_equal; apply IH; cbn; lia].
  all: try solve [repeat f_equal; apply IH; cbn; lia].
Abort.

Eval compute in
  (TypeRules.subst (TypeRules.TVar 0) 1
    (TypeRules.subst (TypeRules.TLam (TypeRules.TVar 1)) 1
      (TypeRules.TVar 1)) =
   TypeRules.subst
    (TypeRules.subst (TypeRules.TVar 0) 0
      (TypeRules.TLam (TypeRules.TVar 1))) 1
    (TypeRules.subst (TypeRules.TVar 0) 2 (TypeRules.TVar 1))).
