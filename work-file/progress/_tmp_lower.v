From Stdlib Require Import List Arith Lia.
Import ListNotations.
Require Import Progress.
Import TypeRules.

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

Lemma lower_sound_aux : forall u k v,
    lower k u = Some v -> lift 1 k v = u.
Proof.
  apply (tsize_strong_ind
    (fun u => forall k v, lower k u = Some v -> lift 1 k v = u)).
  intros u IH k v Hlow.
  destruct u; cbn [lower] in Hlow.
  - cbv [lower] in Hlow.
    destruct (n <? k) eqn:Hlt.
    + inversion Hlow. cbv [lift]. rewrite Hlt. reflexivity.
    + destruct (n =? k) eqn:Heq.
      * discriminate.
      * inversion Hlow. cbv [lift].
        assert (Hge : k <= n) by (apply Nat.ltb_ge; exact Hlt).
        assert (Hneq : n <> k) by (apply Nat.eqb_neq; exact Heq).
        assert (Hpred : (Nat.pred n <? k) = false) by
          (apply Nat.ltb_ge; destruct n; cbn in *; lia).
        rewrite Hpred. f_equal. lia.
  all: try solve [
    repeat match type of Hlow with
    | context [lower ?kk ?uu] =>
        let E := fresh "E" in destruct (lower ?kk ?uu) eqn:E
    end;
    try discriminate;
    inversion Hlow; subst v; cbv [lift];
    repeat match goal with
    | E : lower ?kk ?uu = Some ?vv |- _ =>
        rewrite (IH ?uu ltac:(cbn; lia) ?kk ?vv E)
    end;
    try reflexivity].
  Show.
  Abort.
