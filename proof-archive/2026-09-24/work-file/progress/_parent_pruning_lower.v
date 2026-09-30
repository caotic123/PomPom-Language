Require Import Progress _parent_instance_pruning.
From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations TypeRules Progress._tmp_lower.

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

Print Assumptions prune_lower_mut.


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
Print Assumptions prune_lift1_descent.
