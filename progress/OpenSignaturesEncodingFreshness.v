From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesEncoding.
Require Import OpenSignaturesSubstitution.
Import ListNotations.

Fixpoint db_occurs (k : nat) (t : DB.term) : bool :=
  match t with
  | DB.TVar n => k =? n
  | DB.TSort level => false
  | DB.TPi A B => db_occurs k A || db_occurs (S k) B
  | DB.TLam b => db_occurs (S k) b
  | DB.TApp f a => db_occurs k f || db_occurs k a
  | DB.TSigma A B => db_occurs k A || db_occurs (S k) B
  | DB.TPair a b => db_occurs k a || db_occurs k b
  | DB.TFst p => db_occurs k p
  | DB.TSnd p => db_occurs k p
  | DB.TUnitT => false
  | DB.TUnit => false
  | DB.TUId => false
  | DB.TTag s => false
  | DB.TEnumU => false
  | DB.TNilE => false
  | DB.TConsE tag E => db_occurs k tag || db_occurs k E
  | DB.TEnumT E => db_occurs k E
  | DB.TEZero => false
  | DB.TESucc n => db_occurs k n
  | DB.TEPi level E P => db_occurs k E || db_occurs k P
  | DB.TSwitch level E P p e => db_occurs k E || db_occurs k P || db_occurs k p || db_occurs k e
  | DB.TIDesc IT => db_occurs k IT
  | DB.TIVar i => db_occurs k i
  | DB.TI1 => false
  | DB.TIBot => false
  | DB.TIProd A B => db_occurs k A || db_occurs k B
  | DB.TIPi A D => db_occurs k A || db_occurs k D
  | DB.TISig A D => db_occurs k A || db_occurs k D
  | DB.TIChoice E D => db_occurs k E || db_occurs k D
  | DB.TInterp IT D X => db_occurs k IT || db_occurs k D || db_occurs k X
  | DB.TMuI IT D => db_occurs k IT || db_occurs k D
  | DB.TIn x => db_occurs k x
  | DB.TInd IT D P s i x => db_occurs k IT || db_occurs k D || db_occurs k P || db_occurs k s || db_occurs k i || db_occurs k x
  | DB.TIAll IT D X x P => db_occurs k IT || db_occurs k D || db_occurs k X || db_occurs k x || db_occurs k P
  | DB.THyps IT D X P h x => db_occurs k IT || db_occurs k D || db_occurs k X || db_occurs k P || db_occurs k h || db_occurs k x
  | DB.TClose IT F G => db_occurs k IT || db_occurs k F || db_occurs k G
  | DB.TCloseCase level IT F G i Q b x => db_occurs k IT || db_occurs k F || db_occurs k G || db_occurs k i || db_occurs k Q || db_occurs k b || db_occurs k x
  | DB.TCloseInd IT G P s F i x => db_occurs k IT || db_occurs k G ||
      db_occurs k P || db_occurs k s || db_occurs k F || db_occurs k i || db_occurs k x
  end.

Lemma db_occurs_lift_gap : forall t c, db_occurs c (DB.lift 1 c t) = false.
Proof.
  induction t; intro c; cbn [DB.lift db_occurs];
    repeat match goal with IH : forall c, _ |- _ => rewrite IH end;
    try reflexivity.
  destruct (n <? c) eqn:E; cbn [db_occurs]; apply Nat.eqb_neq;
    [apply Nat.ltb_lt in E|apply Nat.ltb_ge in E]; lia.
Qed.
Lemma encode_var_cons_succ : forall x env v n,
  encode_var (x :: env) v = S n <-> v <> x /\ encode_var env v = n.
Proof.
  intros; cbn [encode_var]; destruct (v =? x) eqn:E;
    [apply Nat.eqb_eq in E|apply Nat.eqb_neq in E]; split; intros; try discriminate; intuition congruence.
Qed.
Lemma encode_occurs : forall t env n,
  db_occurs n (encode env t) = true <->
  exists v, In v (free_vars t) /\ encode_var env v = n.
Proof.
  induction t; intros env v; cbn [encode db_occurs free_vars];
    repeat rewrite Bool.orb_true_iff;
    repeat match goal with IH : forall env n, _ |- _ => rewrite IH end;
    repeat setoid_rewrite in_app_iff;
    repeat setoid_rewrite in_remove_iff;
    repeat setoid_rewrite encode_var_cons_succ;
    try rewrite Nat.eqb_eq;
    repeat match goal with IH : forall env n, _ |- _ => clear IH end;
    cbn [In];
    try solve [firstorder congruence].
  split; intro H.
  - exists n; auto.
  - destruct H as [w [[<-|[]] H]]; symmetry; assumption.
Qed.

Lemma encode_eta_view : forall t env f,
  encode env t = DB.TLam (DB.TApp (DB.lift 1 0 f) (DB.TVar 0)) ->
  exists x body, t = TLam x (TApp body (TVar x)) /\
    ~ In x (free_vars body) /\ encode env body = f.
Proof.
  intros t env f H. destruct t; cbn [encode] in H; try discriminate.
  injection H as Hbody.
  destruct t; cbn [encode] in Hbody; try discriminate.
  injection Hbody as Hfun Harg.
  destruct t2; cbn [encode] in Harg; try discriminate.
  injection Harg as Hindex.
  cbn [encode_var] in Hindex.
  destruct (n =? x) eqn:E; [apply Nat.eqb_eq in E; subst n|discriminate].
  assert (Hfresh : ~ In x (free_vars t1)).
  { intro Hin.
    assert (Hocc : db_occurs 0 (encode (x :: env) t1) = true).
    { apply encode_occurs; exists x; split; [assumption|cbn [encode_var];now rewrite Nat.eqb_refl]. }
    rewrite Hfun, db_occurs_lift_gap in Hocc. discriminate. }
  exists x, t1; split; [reflexivity|]. split; [assumption|].
  rewrite encode_fresh in Hfun by assumption.
  now apply nameless.DBParallelBase.lift_one_injective in Hfun.
Qed.
