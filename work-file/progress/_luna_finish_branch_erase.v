(* Direct, phase-order-independent erasure consumer.  The only premise is
   reflection of a combined path from an erased term to a stable sort. *)

Require Import Progress _tmp_epstep _work_mixed_closure _work_cjoin
  _work_cstep_invariants _glm_injectivity_close_rep.
From Stdlib Require Import List Lia.
Import ListNotations TypeRules.
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

Print Assumptions branch_erase_lift.
Print Assumptions branch_erase_subst.
