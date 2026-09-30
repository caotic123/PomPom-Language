(* A nameless representation used only to reason about alpha equivalence. *)
From Stdlib Require Import List Arith String Bool Lia.
Require Import OpenSignaturesSubstitution.
Require ProofDB.DBCore.
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
  all: f_equal; eauto using encode_var_alpha.
Show.
Abort.
