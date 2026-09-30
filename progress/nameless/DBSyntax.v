(* Revised open-signature calculus: raw syntax and binding operations.
   Independent of TypeRulesCore, which describes the previous calculus.
   The implicit index type is retained explicitly in generic core operators.
   All binders are de Bruijn; only Pi/Sigma codomains and lambda bodies bind. *)
From Stdlib Require Import List Arith String.
Import ListNotations.
Set Implicit Arguments.

Inductive term : Type :=
| TVar (n : nat)
| TSort (k : nat)
| TPi (A : term) (B : term)
| TLam (b : term)
| TApp (f : term) (a : term)
| TSigma (A : term) (B : term)
| TPair (a : term) (b : term)
| TFst (p : term)
| TSnd (p : term)
| TUnitT
| TUnit
| TUId
| TTag (s : string)
| TEnumU
| TNilE
| TConsE (tag : term) (E : term)
| TEnumT (E : term)
| TEZero
| TESucc (n : term)
| TEPi (k : nat) (E : term) (P : term)
| TSwitch (k : nat) (E : term) (P : term) (p : term) (e : term)
| TIDesc (IT : term)
| TIVar (i : term)
| TI1
| TIBot
| TIProd (A : term) (B : term)
| TIPi (A : term) (D : term)
| TISig (A : term) (D : term)
| TIChoice (E : term) (D : term)
| TInterp (IT : term) (D : term) (X : term)
| TMuI (IT : term) (D : term)
| TIn (x : term)
| TInd (IT : term) (D : term) (P : term) (s : term) (i : term) (x : term)
| TIAll (IT : term) (D : term) (X : term) (x : term) (P : term)
| THyps (IT : term) (D : term) (X : term) (P : term) (h : term) (x : term)
| TClose (IT : term) (F : term) (G : term)
| TCloseCase (k : nat) (IT : term) (F : term) (G : term) (i : term) (Q : term) (b : term) (x : term)
| TCloseInd (IT : term) (G : term) (P : term) (s : term) (F : term) (i : term) (x : term).

Fixpoint lift (d cutoff : nat) (t : term) : term :=
  match t with
  | TVar n => if n <? cutoff then TVar n else TVar (d + n)
  | TSort k => TSort k
  | TPi A B => TPi (lift d cutoff A) (lift d (S cutoff) B)
  | TLam b => TLam (lift d (S cutoff) b)
  | TApp f a => TApp (lift d cutoff f) (lift d cutoff a)
  | TSigma A B => TSigma (lift d cutoff A) (lift d (S cutoff) B)
  | TPair a b => TPair (lift d cutoff a) (lift d cutoff b)
  | TFst p => TFst (lift d cutoff p)
  | TSnd p => TSnd (lift d cutoff p)
  | TUnitT => TUnitT
  | TUnit => TUnit
  | TUId => TUId
  | TTag s => TTag s
  | TEnumU => TEnumU
  | TNilE => TNilE
  | TConsE tag E => TConsE (lift d cutoff tag) (lift d cutoff E)
  | TEnumT E => TEnumT (lift d cutoff E)
  | TEZero => TEZero
  | TESucc n => TESucc (lift d cutoff n)
  | TEPi k E P => TEPi k (lift d cutoff E) (lift d cutoff P)
  | TSwitch k E P p e => TSwitch k (lift d cutoff E) (lift d cutoff P) (lift d cutoff p) (lift d cutoff e)
  | TIDesc IT => TIDesc (lift d cutoff IT)
  | TIVar i => TIVar (lift d cutoff i)
  | TI1 => TI1
  | TIBot => TIBot
  | TIProd A B => TIProd (lift d cutoff A) (lift d cutoff B)
  | TIPi A D => TIPi (lift d cutoff A) (lift d cutoff D)
  | TISig A D => TISig (lift d cutoff A) (lift d cutoff D)
  | TIChoice E D => TIChoice (lift d cutoff E) (lift d cutoff D)
  | TInterp IT D X => TInterp (lift d cutoff IT) (lift d cutoff D) (lift d cutoff X)
  | TMuI IT D => TMuI (lift d cutoff IT) (lift d cutoff D)
  | TIn x => TIn (lift d cutoff x)
  | TInd IT D P s i x => TInd (lift d cutoff IT) (lift d cutoff D) (lift d cutoff P) (lift d cutoff s) (lift d cutoff i) (lift d cutoff x)
  | TIAll IT D X x P => TIAll (lift d cutoff IT) (lift d cutoff D) (lift d cutoff X) (lift d cutoff x) (lift d cutoff P)
  | THyps IT D X P h x => THyps (lift d cutoff IT) (lift d cutoff D) (lift d cutoff X) (lift d cutoff P) (lift d cutoff h) (lift d cutoff x)
  | TClose IT F G => TClose (lift d cutoff IT) (lift d cutoff F) (lift d cutoff G)
  | TCloseCase k IT F G i Q b x => TCloseCase k (lift d cutoff IT) (lift d cutoff F) (lift d cutoff G) (lift d cutoff i) (lift d cutoff Q) (lift d cutoff b) (lift d cutoff x)
  | TCloseInd IT G P s F i x => TCloseInd (lift d cutoff IT) (lift d cutoff G) (lift d cutoff P) (lift d cutoff s) (lift d cutoff F) (lift d cutoff i) (lift d cutoff x)
  end.

Fixpoint subst (u : term) (cutoff : nat) (t : term) : term :=
  match t with
  | TVar n => if n <? cutoff then TVar n else if n =? cutoff then lift cutoff 0 u else TVar (Nat.pred n)
  | TSort k => TSort k
  | TPi A B => TPi (subst u cutoff A) (subst u (S cutoff) B)
  | TLam b => TLam (subst u (S cutoff) b)
  | TApp f a => TApp (subst u cutoff f) (subst u cutoff a)
  | TSigma A B => TSigma (subst u cutoff A) (subst u (S cutoff) B)
  | TPair a b => TPair (subst u cutoff a) (subst u cutoff b)
  | TFst p => TFst (subst u cutoff p)
  | TSnd p => TSnd (subst u cutoff p)
  | TUnitT => TUnitT
  | TUnit => TUnit
  | TUId => TUId
  | TTag s => TTag s
  | TEnumU => TEnumU
  | TNilE => TNilE
  | TConsE tag E => TConsE (subst u cutoff tag) (subst u cutoff E)
  | TEnumT E => TEnumT (subst u cutoff E)
  | TEZero => TEZero
  | TESucc n => TESucc (subst u cutoff n)
  | TEPi k E P => TEPi k (subst u cutoff E) (subst u cutoff P)
  | TSwitch k E P p e => TSwitch k (subst u cutoff E) (subst u cutoff P) (subst u cutoff p) (subst u cutoff e)
  | TIDesc IT => TIDesc (subst u cutoff IT)
  | TIVar i => TIVar (subst u cutoff i)
  | TI1 => TI1
  | TIBot => TIBot
  | TIProd A B => TIProd (subst u cutoff A) (subst u cutoff B)
  | TIPi A D => TIPi (subst u cutoff A) (subst u cutoff D)
  | TISig A D => TISig (subst u cutoff A) (subst u cutoff D)
  | TIChoice E D => TIChoice (subst u cutoff E) (subst u cutoff D)
  | TInterp IT D X => TInterp (subst u cutoff IT) (subst u cutoff D) (subst u cutoff X)
  | TMuI IT D => TMuI (subst u cutoff IT) (subst u cutoff D)
  | TIn x => TIn (subst u cutoff x)
  | TInd IT D P s i x => TInd (subst u cutoff IT) (subst u cutoff D) (subst u cutoff P) (subst u cutoff s) (subst u cutoff i) (subst u cutoff x)
  | TIAll IT D X x P => TIAll (subst u cutoff IT) (subst u cutoff D) (subst u cutoff X) (subst u cutoff x) (subst u cutoff P)
  | THyps IT D X P h x => THyps (subst u cutoff IT) (subst u cutoff D) (subst u cutoff X) (subst u cutoff P) (subst u cutoff h) (subst u cutoff x)
  | TClose IT F G => TClose (subst u cutoff IT) (subst u cutoff F) (subst u cutoff G)
  | TCloseCase k IT F G i Q b x => TCloseCase k (subst u cutoff IT) (subst u cutoff F) (subst u cutoff G) (subst u cutoff i) (subst u cutoff Q) (subst u cutoff b) (subst u cutoff x)
  | TCloseInd IT G P s F i x => TCloseInd (subst u cutoff IT) (subst u cutoff G) (subst u cutoff P) (subst u cutoff s) (subst u cutoff F) (subst u cutoff i) (subst u cutoff x)
  end.

(* One-layer compatible closure, used only for definitional congruence.
   R relates each pair of corresponding subterms, including under binders. *)
Inductive compatible (R : term -> term -> Prop) : term -> term -> Prop :=
| cp_TVar : forall n, compatible R (TVar n) (TVar n)
| cp_TSort : forall k, compatible R (TSort k) (TSort k)
| cp_TPi : forall A A' B B', R A A' -> R B B' -> compatible R (TPi A B) (TPi A' B')
| cp_TLam : forall b b', R b b' -> compatible R (TLam b) (TLam b')
| cp_TApp : forall f f' a a', R f f' -> R a a' -> compatible R (TApp f a) (TApp f' a')
| cp_TSigma : forall A A' B B', R A A' -> R B B' -> compatible R (TSigma A B) (TSigma A' B')
| cp_TPair : forall a a' b b', R a a' -> R b b' -> compatible R (TPair a b) (TPair a' b')
| cp_TFst : forall p p', R p p' -> compatible R (TFst p) (TFst p')
| cp_TSnd : forall p p', R p p' -> compatible R (TSnd p) (TSnd p')
| cp_TUnitT : compatible R (TUnitT) (TUnitT)
| cp_TUnit : compatible R (TUnit) (TUnit)
| cp_TUId : compatible R (TUId) (TUId)
| cp_TTag : forall s, compatible R (TTag s) (TTag s)
| cp_TEnumU : compatible R (TEnumU) (TEnumU)
| cp_TNilE : compatible R (TNilE) (TNilE)
| cp_TConsE : forall tag tag' E E', R tag tag' -> R E E' -> compatible R (TConsE tag E) (TConsE tag' E')
| cp_TEnumT : forall E E', R E E' -> compatible R (TEnumT E) (TEnumT E')
| cp_TEZero : compatible R (TEZero) (TEZero)
| cp_TESucc : forall n n', R n n' -> compatible R (TESucc n) (TESucc n')
| cp_TEPi : forall k E E' P P', R E E' -> R P P' -> compatible R (TEPi k E P) (TEPi k E' P')
| cp_TSwitch : forall k E E' P P' p p' e e', R E E' -> R P P' -> R p p' -> R e e' -> compatible R (TSwitch k E P p e) (TSwitch k E' P' p' e')
| cp_TIDesc : forall IT IT', R IT IT' -> compatible R (TIDesc IT) (TIDesc IT')
| cp_TIVar : forall i i', R i i' -> compatible R (TIVar i) (TIVar i')
| cp_TI1 : compatible R (TI1) (TI1)
| cp_TIBot : compatible R (TIBot) (TIBot)
| cp_TIProd : forall A A' B B', R A A' -> R B B' -> compatible R (TIProd A B) (TIProd A' B')
| cp_TIPi : forall A A' D D', R A A' -> R D D' -> compatible R (TIPi A D) (TIPi A' D')
| cp_TISig : forall A A' D D', R A A' -> R D D' -> compatible R (TISig A D) (TISig A' D')
| cp_TIChoice : forall E E' D D', R E E' -> R D D' -> compatible R (TIChoice E D) (TIChoice E' D')
| cp_TInterp : forall IT IT' D D' X X', R IT IT' -> R D D' -> R X X' -> compatible R (TInterp IT D X) (TInterp IT' D' X')
| cp_TMuI : forall IT IT' D D', R IT IT' -> R D D' -> compatible R (TMuI IT D) (TMuI IT' D')
| cp_TIn : forall x x', R x x' -> compatible R (TIn x) (TIn x')
| cp_TInd : forall IT IT' D D' P P' s s' i i' x x', R IT IT' -> R D D' -> R P P' -> R s s' -> R i i' -> R x x' -> compatible R (TInd IT D P s i x) (TInd IT' D' P' s' i' x')
| cp_TIAll : forall IT IT' D D' X X' x x' P P', R IT IT' -> R D D' -> R X X' -> R x x' -> R P P' -> compatible R (TIAll IT D X x P) (TIAll IT' D' X' x' P')
| cp_THyps : forall IT IT' D D' X X' P P' h h' x x', R IT IT' -> R D D' -> R X X' -> R P P' -> R h h' -> R x x' -> compatible R (THyps IT D X P h x) (THyps IT' D' X' P' h' x')
| cp_TClose : forall IT IT' F F' G G', R IT IT' -> R F F' -> R G G' -> compatible R (TClose IT F G) (TClose IT' F' G')
| cp_TCloseCase : forall k IT IT' F F' G G' i i' Q Q' b b' x x', R IT IT' -> R F F' -> R G G' -> R i i' -> R Q Q' -> R b b' -> R x x' -> compatible R (TCloseCase k IT F G i Q b x) (TCloseCase k IT' F' G' i' Q' b' x')
| cp_TCloseInd : forall IT IT' G G' P P' s s' F F' i i' x x', R IT IT' -> R G G' -> R P P' -> R s s' -> R F F' -> R i i' -> R x x' -> compatible R (TCloseInd IT G P s F i x) (TCloseInd IT' G' P' s' F' i' x').

Definition ctx := list term.
Definition arrow (A B : term) := TPi A (lift 1 0 B).
Definition product (A B : term) := TSigma A (lift 1 0 B).
Definition Def (IT : term) := TPi IT (TIDesc (lift 1 0 IT)).
Definition Family (IT : term) := TPi IT (TSort 0).
Definition Bot := TEnumT TNilE.
Definition CloseAt IT F G i := TApp (TClose IT F G) i.
Definition MuAt IT D i := TApp (TMuI IT D) i.
Definition carrier IT G := TClose IT G G.
Definition payload IT F G i := TInterp IT (TApp F i) (carrier IT G).
Definition total IT X := TSigma IT (TApp (lift 1 0 X) (TVar 0)).
Definition motive IT X := TPi (total IT X) (TSort 0).
Definition recursive_method IT X P :=
  TPi IT (TPi (TApp (lift 1 0 X) (TVar 0))
    (TApp (lift 2 0 P) (TPair (TVar 1) (TVar 0)))).

Definition abort (k : nat) (A z : term) :=
  TSwitch k TNilE (TLam (lift 1 0 A)) TUnit z.

Definition close_case_method IT F G i Q :=
  TPi (payload IT F G i)
    (TApp (lift 1 0 Q) (TIn (TVar 0))).

Definition unroll IT F G i x :=
  TCloseCase 0 IT F G i (TLam (lift 1 0 (payload IT F G i)))
    (TLam (TVar 0)) x.

(* P is curried over outer definition, index, and value. *)
Definition close_motive IT G :=
  TPi (Def IT) (TPi (lift 1 0 IT)
    (TPi (CloseAt (lift 2 0 IT) (TVar 1) (lift 2 0 G) (TVar 0))
      (TSort 0))).
Definition diagonal_motive G P :=
  TLam (TApp (TApp (TApp (lift 1 0 P) (lift 1 0 G))
    (TFst (TVar 0))) (TSnd (TVar 0))).
Definition close_ind_method IT G P :=
  TPi (Def IT)
    (TPi (lift 1 0 IT)
      (TPi (payload (lift 2 0 IT) (TVar 1) (lift 2 0 G) (TVar 0))
        (TPi
          (TIAll (lift 3 0 IT) (TApp (TVar 2) (TVar 1))
            (carrier (lift 3 0 IT) (lift 3 0 G)) (TVar 0)
            (diagonal_motive (lift 3 0 G) (lift 3 0 P)))
          (TApp (TApp (TApp (lift 4 0 P) (TVar 3)) (TVar 2))
            (TIn (TVar 1)))))).

Definition mu_ind_method IT D P :=
  TPi IT
    (TPi (TInterp (lift 1 0 IT) (TApp (lift 1 0 D) (TVar 0))
            (TMuI (lift 1 0 IT) (lift 1 0 D)))
      (TPi (TIAll (lift 2 0 IT) (TApp (lift 2 0 D) (TVar 1))
              (TMuI (lift 2 0 IT) (lift 2 0 D)) (TVar 0) (lift 2 0 P))
        (TApp (lift 3 0 P) (TPair (TVar 2) (TIn (TVar 1)))))).

(* B lives under a:A; produce B[c x/a] under x:A'.
   Inserting x below a before substitution preserves the outer context. *)
Definition coerced_codomain c B :=
  subst (TApp (lift 1 0 c) (TVar 0)) 0 (lift 1 1 B).
Definition compose_coercion c d :=
  TLam (TApp (lift 1 0 d) (TApp (lift 1 0 c) (TVar 0))).
Definition pi_coercion c d :=
  TLam (TLam (TApp (lift 1 1 d)
    (TApp (TVar 1) (TApp (lift 2 0 c) (TVar 0))))).
Definition close_coercion (IT F H G i q : term) :=
  TLam (TIn (TApp (lift 1 0 q)
    (unroll (lift 1 0 IT) (lift 1 0 F) (lift 1 0 G)
      (lift 1 0 i) (TVar 0)))).

Fixpoint enum_position (n : nat) : term :=
  match n with 0 => TEZero | S n => TESucc (enum_position n) end.
Fixpoint tuple (ts : list term) : term :=
  match ts with [] => TUnit | t :: ts => TPair t (tuple ts) end.
