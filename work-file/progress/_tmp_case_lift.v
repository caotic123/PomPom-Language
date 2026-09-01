Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma enum_index_lift_local : forall a d k,
    enum_index (lift d k a) = enum_index a.
Proof.
  induction a; intros d q; cbn [lift enum_index]; try reflexivity.
  - destruct (Nat.ltb n q); reflexivity.
  - rewrite IHa. reflexivity.
Qed.

Lemma pdev_lift_branches_local : forall bs d k,
    (forall c b, In (c,b) bs ->
      pdev (lift d k c) = lift d k (pdev c) /\
      pdev (lift d (S k) b) = lift d (S k) (pdev b)) ->
    map (fun '(c,b) => (pdev c, pdev b))
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs) =
    map (fun '(c,b) => (lift d k (pdev c), lift d (S k) (pdev b))) bs.
Proof.
  induction bs as [|[c b] bs IH]; intros d k H; cbn; [reflexivity |].
  destruct (H c b (or_introl eq_refl)) as [Hc Hb].
  rewrite Hc, Hb, IH.
  - reflexivity.
  - intros c' b' Hin. exact (H c' b' (or_intror Hin)).
Qed.

Lemma pdev_lift_selected_branches_local : forall bs d k,
    (forall c b, In (c,b) bs ->
      pdev (lift d (S k) b) = lift d (S k) (pdev b)) ->
    map (fun '(c,b) => (c, pdev b))
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs) =
    map (fun '(c,b) => (lift d k c, lift d (S k) (pdev b))) bs.
Proof.
  induction bs as [|[c b] bs IH]; intros d k H; cbn; [reflexivity |].
  rewrite (H c b (or_introl eq_refl)), IH.
  - reflexivity.
  - intros c' b' Hin. exact (H c' b' (or_intror Hin)).
Qed.

Lemma first_branch_lift_selected_local : forall bs n d k,
    first_branch n
      (map (fun '(c,b) => (lift d k c, lift d (S k) (pdev b))) bs) =
    option_map (lift d (S k))
      (first_branch n (map (fun '(c,b) => (c, pdev b)) bs)).
Proof.
  induction bs as [|[c b] bs IH]; intros n d k; cbn; [reflexivity |].
  rewrite enum_index_lift_local.
  destruct (enum_index c); [destruct (Nat.eqb n0 n) |]; cbn;
    try reflexivity; apply IH.
Qed.

Lemma pdev_lift_case_local : forall M Q bs,
    (forall d k, pdev (lift d k M) = lift d k (pdev M)) ->
    (forall d k, pdev (lift d k Q) = lift d k (pdev Q)) ->
    (forall c b, In (c,b) bs -> forall d k,
      pdev (lift d k c) = lift d k (pdev c) /\
      pdev (lift d (S k) b) = lift d (S k) (pdev b)) ->
    forall d k,
      pdev (lift d k (TCase M Q bs)) =
      lift d k (pdev (TCase M Q bs)).
Proof.
  intros M Q bs HM HQ Hbs d k.
  pose proof (HM d k) as HMk.
  pose proof (HQ d k) as HQk.
  pose proof (pdev_lift_branches_local bs d k
    ltac:(intros c b Hin; apply Hbs; exact Hin)) as Hdev.
  pose proof (pdev_lift_selected_branches_local bs d k
    ltac:(intros c b Hin; apply (proj2 (Hbs c b Hin d k)))) as Hsel.
  assert (Hdev' :
      map (fun '(c,b) => (pdev c,pdev b))
        (map (fun '(c,b) => (lift d k c,lift d (S k) b)) bs) =
      map (fun '(c,b) => (lift d k c,lift d (S k) b))
        (map (fun '(c,b) => (pdev c,pdev b)) bs)).
  { rewrite Hdev, map_map. apply map_ext. intros [c b]. reflexivity. }
  destruct M; cbn [lift pdev] in HMk |- *;
    try solve [rewrite HQk, Hdev'; f_equal; exact HMk].
  - destruct (Nat.ltb n k); cbn [lift pdev] in HMk |- *;
      rewrite HQk, Hdev'; f_equal; exact HMk.
  - destruct M; cbn [lift pdev] in HMk |- *;
      try solve [rewrite HQk, Hdev'; f_equal; exact HMk].
    + destruct (Nat.ltb n k); cbn [lift pdev] in HMk |- *;
        rewrite HQk, Hdev'; f_equal; exact HMk.
    + rewrite enum_index_lift_local, Hsel.
      destruct (enum_index M1) as [n|] eqn:Hidx.
      * rewrite first_branch_lift_selected_local.
        destruct (first_branch n (map (fun '(c,b) => (c,pdev b)) bs))
          as [body|] eqn:Hfirst; cbn.
        -- injection HMk as Ha Hxs.
           rewrite Hxs, lift_subst_zero_comm. reflexivity.
        -- rewrite HMk, HQk, Hdev'. reflexivity.
      * rewrite HMk, HQk, Hdev'. reflexivity.
Qed.
