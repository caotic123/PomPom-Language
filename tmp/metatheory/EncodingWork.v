(* A nameless representation used only to reason about alpha equivalence. *)
From Stdlib Require Import List Arith String Bool Lia.
Require Import OpenSignaturesSubstitution.
Require ProofDB.DBParallelBase.
Import ListNotations.
Module DB := ProofDB.DBSyntax.

Fixpoint encode_var (env : list nat) (x : nat) : nat :=
  match env with [] => x | y :: env => if x =? y then 0 else S (encode_var env x) end.

Fixpoint encode (env : list nat) (t : term) : DB.term :=
  match t with
  | TVar n => DB.TVar (encode_var env n)
  | TSort k => DB.TSort k
  | TPi x A B => DB.TPi (encode env A) (encode (x :: env) B)
  | TLam x b => DB.TLam (encode (x :: env) b)
  | TApp f a => DB.TApp (encode env f) (encode env a)
  | TSigma x A B => DB.TSigma (encode env A) (encode (x :: env) B)
  | TPair a b => DB.TPair (encode env a) (encode env b)
  | TFst p => DB.TFst (encode env p)
  | TSnd p => DB.TSnd (encode env p)
  | TUnitT => DB.TUnitT
  | TUnit => DB.TUnit
  | TUId => DB.TUId
  | TTag s => DB.TTag s
  | TEnumU => DB.TEnumU
  | TNilE => DB.TNilE
  | TConsE tag E => DB.TConsE (encode env tag) (encode env E)
  | TEnumT E => DB.TEnumT (encode env E)
  | TEZero => DB.TEZero
  | TESucc n => DB.TESucc (encode env n)
  | TEPi k E P => DB.TEPi k (encode env E) (encode env P)
  | TSwitch k E P p e => DB.TSwitch k (encode env E) (encode env P) (encode env p) (encode env e)
  | TIDesc IT => DB.TIDesc (encode env IT)
  | TIVar i => DB.TIVar (encode env i)
  | TI1 => DB.TI1
  | TIBot => DB.TIBot
  | TIProd A B => DB.TIProd (encode env A) (encode env B)
  | TIPi A D => DB.TIPi (encode env A) (encode env D)
  | TISig A D => DB.TISig (encode env A) (encode env D)
  | TIChoice E D => DB.TIChoice (encode env E) (encode env D)
  | TInterp IT D X => DB.TInterp (encode env IT) (encode env D) (encode env X)
  | TMuI IT D => DB.TMuI (encode env IT) (encode env D)
  | TIn x => DB.TIn (encode env x)
  | TInd IT D P s i x => DB.TInd (encode env IT) (encode env D) (encode env P) (encode env s) (encode env i) (encode env x)
  | TIAll IT D X x P => DB.TIAll (encode env IT) (encode env D) (encode env X) (encode env x) (encode env P)
  | THyps IT D X P h x => DB.THyps (encode env IT) (encode env D) (encode env X) (encode env P) (encode env h) (encode env x)
  | TClose IT F G => DB.TClose (encode env IT) (encode env F) (encode env G)
  | TCloseCase k IT F G i Q b x => DB.TCloseCase k (encode env IT) (encode env F) (encode env G) (encode env i) (encode env Q) (encode env b) (encode env x)
  | TCloseInd IT G P s F i x => DB.TCloseInd (encode env IT) (encode env G) (encode env P) (encode env s) (encode env F) (encode env i) (encode env x)
  end.

Lemma encode_var_alpha : forall xs ys x y,
  List.length xs = List.length ys ->
  (alpha_var xs ys x y = true <-> encode_var xs x = encode_var ys y).
Proof.
  induction xs as [|a xs IH]; destruct ys as [|b ys];
    intros x y Hlen; cbn in *; try discriminate.
  - apply Nat.eqb_eq.
  - destruct (x =? a), (y =? b); cbn; try solve [split; congruence].
    rewrite IH by lia. split; congruence.
Qed.

Lemma encode_alpha : forall t u xs ys,
  List.length xs = List.length ys -> alpha_eqb_in xs ys t u = true ->
  encode xs t = encode ys u.
Proof.
  induction t; destruct u; intros xs ys Hlen Ha;
    cbn [alpha_eqb_in] in Ha; try discriminate;
    repeat rewrite Bool.andb_true_iff in Ha;
    repeat rewrite Nat.eqb_eq in Ha;
    repeat rewrite String.eqb_eq in Ha;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    cbn [encode]; try solve [f_equal; assumption | reflexivity].
  all: f_equal; try solve [eauto].
  { now apply encode_var_alpha. }
  all: match goal with IH : forall u xs ys, _ -> _ -> encode xs ?tm = encode ys u
      |- encode _ ?tm = encode _ _ => apply IH; [cbn; lia|assumption] end.
Qed.

Lemma encode_alpha_inverse : forall t u xs ys,
  List.length xs = List.length ys -> encode xs t = encode ys u ->
  alpha_eqb_in xs ys t u = true.
Proof.
  induction t; destruct u; intros xs ys Hlen Heq;
    cbn [encode] in Heq; try discriminate; inversion Heq; subst;
    cbn [alpha_eqb_in]; repeat rewrite Bool.andb_true_iff;
    repeat rewrite Nat.eqb_eq; repeat rewrite String.eqb_eq;
    repeat split; try reflexivity; try solve [eauto].
  { apply encode_var_alpha; assumption. }
  all: match goal with IH : forall u xs ys, _ -> _ -> alpha_eqb_in xs ys ?tm u = true
      |- alpha_eqb_in _ _ ?tm _ = true => apply IH; [cbn; lia|assumption] end.
Qed.

Theorem encode_alpha_iff : forall t u,
  alpha_equiv t u <-> encode [] t = encode [] u.
Proof. intros; split; [apply encode_alpha|apply encode_alpha_inverse]; reflexivity. Qed.

Lemma encode_var_insert : forall pre env x v,
  (v = x -> In v pre) ->
  encode_var (pre ++ x :: env) v =
    (if encode_var (pre ++ env) v <? List.length pre
     then encode_var (pre ++ env) v else S (encode_var (pre ++ env) v)).
Proof.
  induction pre as [|a pre IH]; intros env x v H; cbn [encode_var List.app List.length].
  - destruct (v =? x) eqn:E; [apply Nat.eqb_eq in E; specialize (H E); contradiction|reflexivity].
  - destruct (v =? a) eqn:E; [reflexivity|].
    change (S (encode_var (pre ++ x :: env) v) =
      (if encode_var (pre ++ env) v <? List.length pre
       then S (encode_var (pre ++ env) v) else S (S (encode_var (pre ++ env) v)))).
    rewrite IH.
    + destruct (encode_var (pre ++ env) v <? List.length pre); reflexivity.
    + intros Hx. specialize (H Hx). cbn in H. destruct H as [H|H]; [subst; rewrite Nat.eqb_refl in E; discriminate|exact H].
Qed.

Lemma encode_lift_env : forall t pre env x,
  (forall v, In v (free_vars t) -> v = x -> In v pre) ->
  encode (pre ++ x :: env) t = DB.lift 1 (List.length pre) (encode (pre ++ env) t).
Proof.
  induction t; intros pre env freshvar H; cbn [encode DB.lift]; f_equal;
    try solve [eauto]; cbn [free_vars] in H.
  { rewrite encode_var_insert by (intros; apply H; [cbn;auto|assumption]).
    destruct (encode_var (pre ++ env) n <? List.length pre); reflexivity. }
  all: try solve [match goal with
    | IH : forall pre env x, _ -> encode _ ?tm = _ |- encode _ ?tm = _ =>
      apply IH; intros; apply H; [repeat rewrite in_app_iff; tauto|assumption]
    end].
  all: match goal with |- encode _ ?tm = _ =>
    change (encode ((x :: pre) ++ freshvar :: env) tm =
      DB.lift 1 (List.length (x :: pre)) (encode ((x :: pre) ++ env) tm)) end;
    first [apply IHt|apply IHt2]; intros v Hv Hx;
    destruct (Nat.eq_dec v x) as [->|Hvn]; [now left|right; apply H; [|exact Hx]];
    try (apply in_or_app; right); apply in_in_remove; [congruence|exact Hv].

Qed.

Corollary encode_fresh : forall t env x, ~ In x (free_vars t) ->
  encode (x :: env) t = DB.lift 1 0 (encode env t).
Proof.
  intros t env x H. exact (encode_lift_env t [] env x ltac:(intros v Hv ->; contradiction)).
Qed.

Definition db_up (tau : nat -> DB.term) (n : nat) : DB.term :=
  match n with 0 => DB.TVar 0 | S m => DB.lift 1 0 (tau m) end.

Fixpoint db_sub (tau : nat -> DB.term) (t : DB.term) : DB.term :=
  match t with
  | DB.TVar n => tau n
  | DB.TSort k => DB.TSort k
  | DB.TPi A B => DB.TPi (db_sub tau A) (db_sub (db_up tau) B)
  | DB.TLam b => DB.TLam (db_sub (db_up tau) b)
  | DB.TApp f a => DB.TApp (db_sub tau f) (db_sub tau a)
  | DB.TSigma A B => DB.TSigma (db_sub tau A) (db_sub (db_up tau) B)
  | DB.TPair a b => DB.TPair (db_sub tau a) (db_sub tau b)
  | DB.TFst p => DB.TFst (db_sub tau p)
  | DB.TSnd p => DB.TSnd (db_sub tau p)
  | DB.TUnitT => DB.TUnitT
  | DB.TUnit => DB.TUnit
  | DB.TUId => DB.TUId
  | DB.TTag s => DB.TTag s
  | DB.TEnumU => DB.TEnumU
  | DB.TNilE => DB.TNilE
  | DB.TConsE tag E => DB.TConsE (db_sub tau tag) (db_sub tau E)
  | DB.TEnumT E => DB.TEnumT (db_sub tau E)
  | DB.TEZero => DB.TEZero
  | DB.TESucc n => DB.TESucc (db_sub tau n)
  | DB.TEPi k E P => DB.TEPi k (db_sub tau E) (db_sub tau P)
  | DB.TSwitch k E P p e => DB.TSwitch k (db_sub tau E) (db_sub tau P) (db_sub tau p) (db_sub tau e)
  | DB.TIDesc IT => DB.TIDesc (db_sub tau IT)
  | DB.TIVar i => DB.TIVar (db_sub tau i)
  | DB.TI1 => DB.TI1
  | DB.TIBot => DB.TIBot
  | DB.TIProd A B => DB.TIProd (db_sub tau A) (db_sub tau B)
  | DB.TIPi A D => DB.TIPi (db_sub tau A) (db_sub tau D)
  | DB.TISig A D => DB.TISig (db_sub tau A) (db_sub tau D)
  | DB.TIChoice E D => DB.TIChoice (db_sub tau E) (db_sub tau D)
  | DB.TInterp IT D X => DB.TInterp (db_sub tau IT) (db_sub tau D) (db_sub tau X)
  | DB.TMuI IT D => DB.TMuI (db_sub tau IT) (db_sub tau D)
  | DB.TIn x => DB.TIn (db_sub tau x)
  | DB.TInd IT D P s i x => DB.TInd (db_sub tau IT) (db_sub tau D) (db_sub tau P) (db_sub tau s) (db_sub tau i) (db_sub tau x)
  | DB.TIAll IT D X x P => DB.TIAll (db_sub tau IT) (db_sub tau D) (db_sub tau X) (db_sub tau x) (db_sub tau P)
  | DB.THyps IT D X P h x => DB.THyps (db_sub tau IT) (db_sub tau D) (db_sub tau X) (db_sub tau P) (db_sub tau h) (db_sub tau x)
  | DB.TClose IT F G => DB.TClose (db_sub tau IT) (db_sub tau F) (db_sub tau G)
  | DB.TCloseCase k IT F G i Q b x => DB.TCloseCase k (db_sub tau IT) (db_sub tau F) (db_sub tau G) (db_sub tau i) (db_sub tau Q) (db_sub tau b) (db_sub tau x)
  | DB.TCloseInd IT G P s F i x => DB.TCloseInd (db_sub tau IT) (db_sub tau G) (db_sub tau P) (db_sub tau s) (db_sub tau F) (db_sub tau i) (db_sub tau x)
  end.

Lemma encode_bind_substitution : forall b x env env' sigma tau,
  (forall v, In v (remove Nat.eq_dec x (free_vars b)) ->
    encode env' (sigma v) = tau (encode_var env v)) ->
  forall v, In v (free_vars b) ->
  encode (substitution_binder sigma x b :: env')
    (bind_substitution sigma x (substitution_binder sigma x b) v) =
  db_up tau (encode_var (x :: env) v).
Proof.
  intros b x env env' sigma tau H v Hv. unfold bind_substitution.
  cbn [encode_var]. destruct (v =? x) eqn:E.
  - cbn [encode encode_var db_up]. now rewrite Nat.eqb_refl.
  - cbn [db_up]. rewrite encode_fresh.
    + f_equal. apply H, in_in_remove; [now apply Nat.eqb_neq in E|assumption].
    + apply substitution_binder_fresh; [assumption|now apply Nat.eqb_neq in E].
Qed.

Theorem encode_substitute : forall t env env' sigma tau,
  (forall v, In v (free_vars t) -> encode env' (sigma v) = tau (encode_var env v)) ->
  encode env' (substitute sigma t) = db_sub tau (encode env t).
Proof.
  induction t; intros env env' sigma tau H; cbn [substitute encode db_sub];
    try reflexivity; f_equal; cbn [free_vars] in H.
  { apply H. now left. }
  all: try solve [match goal with
    | IH : forall env env' sigma tau, _ -> encode _ (substitute _ ?tm) = _
      |- encode _ (substitute _ ?tm) = _ =>
      apply IH; intros; apply H; repeat rewrite in_app_iff; tauto end].
  all: first [apply IHt|apply IHt2]; apply encode_bind_substitution;
    intros; apply H; try (apply in_or_app; right); assumption.
Qed.

Lemma db_sub_ext : forall t sigma tau, (forall n, sigma n = tau n) ->
  db_sub sigma t = db_sub tau t.
Proof.
  induction t; intros sigma tau H; cbn [db_sub]; try reflexivity;
    try apply H; f_equal; try solve [auto].
  all: first [apply IHt|apply IHt2]; intros [|n]; cbn [db_up]; [reflexivity|now rewrite H].
Qed.
Definition db_single (u : DB.term) c n :=
  if n <? c then DB.TVar n else if n =? c then DB.lift c 0 u else DB.TVar (Nat.pred n).
Lemma db_single_up : forall u c n, db_up (db_single u c) n = db_single u (S c) n.
Proof.
  intros u c [|n]; [reflexivity|]. unfold db_up, db_single.
  change (DB.lift 1 0 (if n <? c then DB.TVar n else
    if n =? c then DB.lift c 0 u else DB.TVar (Nat.pred n)) =
    (if n <? c then DB.TVar (S n) else if n =? c
     then DB.lift (S c) 0 u else DB.TVar n)).
  destruct (n <? c) eqn:E; [reflexivity|]. destruct (n =? c) eqn:Eq.
  - apply ProofDB.DBParallelBase.lift_fuse_zero. lia.
  - apply Nat.ltb_ge in E; apply Nat.eqb_neq in Eq.
    cbn [DB.lift]. destruct n; [lia|reflexivity].
Qed.
Lemma db_sub_single : forall t u c, db_sub (db_single u c) t = DB.subst u c t.
Proof.
  induction t; intros u c; cbn [db_sub DB.subst]; try reflexivity;
    f_equal; try solve [auto].
  all: rewrite (db_sub_ext _ _ (db_single u (S c))) by apply db_single_up;
    auto.
Qed.
Theorem encode_subst : forall b env x u,
  encode env (subst u x b) = DB.subst (encode env u) 0 (encode (x :: env) b).
Proof.
  intros b env x u. rewrite <- db_sub_single. unfold subst.
  apply encode_substitute. intros v Hv. cbn [encode_var].
  destruct (v =? x) eqn:E; [|reflexivity].
  change (encode env u = DB.lift 0 0 (encode env u)).
  symmetry. apply ProofDB.DBParallelBase.lift_zero_id.
Qed.
