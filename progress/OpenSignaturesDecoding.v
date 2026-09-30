From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesEncodingTyping.
Import ListNotations.

Fixpoint db_scoped (depth : nat) (t : DB.term) : Prop :=
  match t with
  | DB.TVar n => n < depth
  | DB.TSort k => True
  | DB.TPi A B => db_scoped depth A /\ db_scoped (S depth) B
  | DB.TLam b => db_scoped (S depth) b
  | DB.TApp f a => db_scoped depth f /\ db_scoped depth a
  | DB.TSigma A B => db_scoped depth A /\ db_scoped (S depth) B
  | DB.TPair a b => db_scoped depth a /\ db_scoped depth b
  | DB.TFst p => db_scoped depth p
  | DB.TSnd p => db_scoped depth p
  | DB.TUnitT => True
  | DB.TUnit => True
  | DB.TUId => True
  | DB.TTag s => True
  | DB.TEnumU => True
  | DB.TNilE => True
  | DB.TConsE tag E => db_scoped depth tag /\ db_scoped depth E
  | DB.TEnumT E => db_scoped depth E
  | DB.TEZero => True
  | DB.TESucc n => db_scoped depth n
  | DB.TEPi k E P => db_scoped depth E /\ db_scoped depth P
  | DB.TSwitch k E P p e => db_scoped depth E /\ db_scoped depth P /\ db_scoped depth p /\ db_scoped depth e
  | DB.TIDesc IT => db_scoped depth IT
  | DB.TIVar i => db_scoped depth i
  | DB.TI1 => True
  | DB.TIBot => True
  | DB.TIProd A B => db_scoped depth A /\ db_scoped depth B
  | DB.TIPi A D => db_scoped depth A /\ db_scoped depth D
  | DB.TISig A D => db_scoped depth A /\ db_scoped depth D
  | DB.TIChoice E D => db_scoped depth E /\ db_scoped depth D
  | DB.TInterp IT D X => db_scoped depth IT /\ db_scoped depth D /\ db_scoped depth X
  | DB.TMuI IT D => db_scoped depth IT /\ db_scoped depth D
  | DB.TIn x => db_scoped depth x
  | DB.TInd IT D P s i x => db_scoped depth IT /\ db_scoped depth D /\ db_scoped depth P /\ db_scoped depth s /\ db_scoped depth i /\ db_scoped depth x
  | DB.TIAll IT D X x P => db_scoped depth IT /\ db_scoped depth D /\ db_scoped depth X /\ db_scoped depth x /\ db_scoped depth P
  | DB.THyps IT D X P h x => db_scoped depth IT /\ db_scoped depth D /\ db_scoped depth X /\ db_scoped depth P /\ db_scoped depth h /\ db_scoped depth x
  | DB.TClose IT F G => db_scoped depth IT /\ db_scoped depth F /\ db_scoped depth G
  | DB.TCloseCase k IT F G i Q b x => db_scoped depth IT /\ db_scoped depth F /\ db_scoped depth G /\ db_scoped depth i /\ db_scoped depth Q /\ db_scoped depth b /\ db_scoped depth x
  | DB.TCloseInd IT G P s F i x => db_scoped depth IT /\ db_scoped depth G /\ db_scoped depth P /\ db_scoped depth s /\ db_scoped depth F /\ db_scoped depth i /\ db_scoped depth x
  end.

Lemma sd_typing_scoped : forall Gamma t A, nameless.DBTyping.typing Gamma t A ->
  db_scoped (List.length Gamma) t.
Proof.
  intros Gamma t A H; induction H; cbn [db_scoped List.length] in *; tauto || idtac.
  apply nth_error_Some. rewrite H0. discriminate.
Qed.
Lemma sd_type_scoped : forall Gamma t A, nameless.DBTyping.typing Gamma t A ->
  db_scoped (List.length Gamma) A.
Proof.
  intros Gamma t A H. destruct (nameless.DBWeakening.type_correctness _ _ _ H) as [k HA].
  eapply sd_typing_scoped;exact HA.
Qed.

Fixpoint decode (env : list nat) (t : DB.term) : term :=
  match t with
  | DB.TVar n => TVar (nth n env 0)
  | DB.TSort k => TSort k
  | DB.TPi A B => TPi (fresh_id env) (decode env A) (decode (fresh_id env :: env) B)
  | DB.TLam b => TLam (fresh_id env) (decode (fresh_id env :: env) b)
  | DB.TApp f a => TApp (decode env f) (decode env a)
  | DB.TSigma A B => TSigma (fresh_id env) (decode env A) (decode (fresh_id env :: env) B)
  | DB.TPair a b => TPair (decode env a) (decode env b)
  | DB.TFst p => TFst (decode env p)
  | DB.TSnd p => TSnd (decode env p)
  | DB.TUnitT => TUnitT
  | DB.TUnit => TUnit
  | DB.TUId => TUId
  | DB.TTag s => TTag s
  | DB.TEnumU => TEnumU
  | DB.TNilE => TNilE
  | DB.TConsE tag E => TConsE (decode env tag) (decode env E)
  | DB.TEnumT E => TEnumT (decode env E)
  | DB.TEZero => TEZero
  | DB.TESucc n => TESucc (decode env n)
  | DB.TEPi k E P => TEPi k (decode env E) (decode env P)
  | DB.TSwitch k E P p e => TSwitch k (decode env E) (decode env P) (decode env p) (decode env e)
  | DB.TIDesc IT => TIDesc (decode env IT)
  | DB.TIVar i => TIVar (decode env i)
  | DB.TI1 => TI1
  | DB.TIBot => TIBot
  | DB.TIProd A B => TIProd (decode env A) (decode env B)
  | DB.TIPi A D => TIPi (decode env A) (decode env D)
  | DB.TISig A D => TISig (decode env A) (decode env D)
  | DB.TIChoice E D => TIChoice (decode env E) (decode env D)
  | DB.TInterp IT D X => TInterp (decode env IT) (decode env D) (decode env X)
  | DB.TMuI IT D => TMuI (decode env IT) (decode env D)
  | DB.TIn x => TIn (decode env x)
  | DB.TInd IT D P s i x => TInd (decode env IT) (decode env D) (decode env P) (decode env s) (decode env i) (decode env x)
  | DB.TIAll IT D X x P => TIAll (decode env IT) (decode env D) (decode env X) (decode env x) (decode env P)
  | DB.THyps IT D X P h x => THyps (decode env IT) (decode env D) (decode env X) (decode env P) (decode env h) (decode env x)
  | DB.TClose IT F G => TClose (decode env IT) (decode env F) (decode env G)
  | DB.TCloseCase k IT F G i Q b x => TCloseCase k (decode env IT) (decode env F) (decode env G) (decode env i) (decode env Q) (decode env b) (decode env x)
  | DB.TCloseInd IT G P s F i x => TCloseInd (decode env IT) (decode env G) (decode env P) (decode env s) (decode env F) (decode env i) (decode env x)
  end.

Lemma decode_universe_le : forall A B, nameless.DBTyping.universe_le A B -> forall env,
  universe_le (decode env A) (decode env B).
Proof. intros A B H; induction H; intros; cbn [decode]; auto using universe_le. Qed.

Lemma encode_var_nth : forall env n, NoDup env -> n < List.length env ->
  encode_var env (nth n env 0) = n.
Proof.
  induction env as [|x env IH]; intros [|n] Hnd Hn; cbn in *; try lia.
  - now rewrite Nat.eqb_refl.
  - inversion Hnd as [|? ? Hnot Htail]; subst.
    assert (Hneq : Nat.eqb (nth n env 0) x = false).
    { apply Nat.eqb_neq; intro E. apply Hnot. rewrite <- E. apply nth_In;lia. }
    rewrite Hneq, IH; auto;lia.
Qed.

Theorem encode_decode : forall t env,
  NoDup env -> db_scoped (List.length env) t -> encode env (decode env t) = t.
Proof.
  induction t; intros env Hnd Hscope; cbn [db_scoped] in Hscope;
    cbn [decode encode]; try reflexivity;
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
  { f_equal;now apply encode_var_nth. }
  all: f_equal; auto.
  all: apply IHt || apply IHt2; [constructor;auto using fresh_id_not_in|assumption].
Qed.

Lemma decode_sort : forall env k, decode env (DB.TSort k) = TSort k.
Proof. reflexivity. Qed.
