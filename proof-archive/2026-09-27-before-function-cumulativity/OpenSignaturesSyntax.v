(* Core terms use stable natural-number binding IDs. Context extension never
   shifts an existing reference. Pi, Sigma and lambda record their binder IDs. *)
From Stdlib Require Import List Arith String FMapAVL Structures.OrderedTypeEx.
Import ListNotations.
Set Implicit Arguments.

Inductive term : Type :=
| TVar (n : nat)
| TSort (k : nat)
| TPi (x : nat) (A : term) (B : term)
| TLam (x : nat) (b : term)
| TApp (f : term) (a : term)
| TSigma (x : nat) (A : term) (B : term)
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

Fixpoint vars (t : term) : list nat :=
  match t with
  | TVar n => [n]
  | TSort k => []
  | TPi x A B => x :: (vars A ++ vars B)
  | TLam x b => x :: vars b
  | TApp f a => vars f ++ vars a
  | TSigma x A B => x :: (vars A ++ vars B)
  | TPair a b => vars a ++ vars b
  | TFst p => vars p
  | TSnd p => vars p
  | TUnitT  => []
  | TUnit  => []
  | TUId  => []
  | TTag s => []
  | TEnumU  => []
  | TNilE  => []
  | TConsE tag E => vars tag ++ vars E
  | TEnumT E => vars E
  | TEZero  => []
  | TESucc n => vars n
  | TEPi k E P => vars E ++ vars P
  | TSwitch k E P p e => vars E ++ vars P ++ vars p ++ vars e
  | TIDesc IT => vars IT
  | TIVar i => vars i
  | TI1  => []
  | TIBot  => []
  | TIProd A B => vars A ++ vars B
  | TIPi A D => vars A ++ vars D
  | TISig A D => vars A ++ vars D
  | TIChoice E D => vars E ++ vars D
  | TInterp IT D X => vars IT ++ vars D ++ vars X
  | TMuI IT D => vars IT ++ vars D
  | TIn x => vars x
  | TInd IT D P s i x => vars IT ++ vars D ++ vars P ++ vars s ++ vars i ++ vars x
  | TIAll IT D X x P => vars IT ++ vars D ++ vars X ++ vars x ++ vars P
  | THyps IT D X P h x => vars IT ++ vars D ++ vars X ++ vars P ++ vars h ++ vars x
  | TClose IT F G => vars IT ++ vars F ++ vars G
  | TCloseCase k IT F G i Q b x => vars IT ++ vars F ++ vars G ++ vars i ++ vars Q ++ vars b ++ vars x
  | TCloseInd IT G P s F i x => vars IT ++ vars G ++ vars P ++ vars s ++ vars F ++ vars i ++ vars x
  end.

Fixpoint free_vars (t : term) : list nat :=
  match t with
  | TVar n => [n]
  | TSort k => []
  | TPi x A B => free_vars A ++ remove Nat.eq_dec x (free_vars B)
  | TLam x b => remove Nat.eq_dec x (free_vars b)
  | TApp f a => free_vars f ++ free_vars a
  | TSigma x A B => free_vars A ++ remove Nat.eq_dec x (free_vars B)
  | TPair a b => free_vars a ++ free_vars b
  | TFst p => free_vars p
  | TSnd p => free_vars p
  | TUnitT  => []
  | TUnit  => []
  | TUId  => []
  | TTag s => []
  | TEnumU  => []
  | TNilE  => []
  | TConsE tag E => free_vars tag ++ free_vars E
  | TEnumT E => free_vars E
  | TEZero  => []
  | TESucc n => free_vars n
  | TEPi k E P => free_vars E ++ free_vars P
  | TSwitch k E P p e => free_vars E ++ free_vars P ++ free_vars p ++ free_vars e
  | TIDesc IT => free_vars IT
  | TIVar i => free_vars i
  | TI1  => []
  | TIBot  => []
  | TIProd A B => free_vars A ++ free_vars B
  | TIPi A D => free_vars A ++ free_vars D
  | TISig A D => free_vars A ++ free_vars D
  | TIChoice E D => free_vars E ++ free_vars D
  | TInterp IT D X => free_vars IT ++ free_vars D ++ free_vars X
  | TMuI IT D => free_vars IT ++ free_vars D
  | TIn x => free_vars x
  | TInd IT D P s i x => free_vars IT ++ free_vars D ++ free_vars P ++ free_vars s ++ free_vars i ++ free_vars x
  | TIAll IT D X x P => free_vars IT ++ free_vars D ++ free_vars X ++ free_vars x ++ free_vars P
  | THyps IT D X P h x => free_vars IT ++ free_vars D ++ free_vars X ++ free_vars P ++ free_vars h ++ free_vars x
  | TClose IT F G => free_vars IT ++ free_vars F ++ free_vars G
  | TCloseCase k IT F G i Q b x => free_vars IT ++ free_vars F ++ free_vars G ++ free_vars i ++ free_vars Q ++ free_vars b ++ free_vars x
  | TCloseInd IT G P s F i x => free_vars IT ++ free_vars G ++ free_vars P ++ free_vars s ++ free_vars F ++ free_vars i ++ free_vars x
  end.

Definition fresh_id (ids : list nat) := S (fold_right Nat.max 0 ids).
Definition fresh (ts : list term) := fresh_id (flat_map vars ts).

(* Substitution is structural. When a binder could capture a free variable
   in a replacement, give only that binder a fresh ID and carry the renaming
   in sigma. Free/context IDs are never renumbered. *)
Definition substitution_binder (sigma : nat -> term) (x : nat) (b : term) :=
  let avoid := flat_map (fun y => free_vars (sigma y))
    (remove Nat.eq_dec x (free_vars b)) in
  if existsb (Nat.eqb x) avoid
  then fresh_id (vars b ++ avoid ++ [x]) else x.
Definition bind_substitution (sigma : nat -> term) (x y : nat) :=
  fun z => if Nat.eqb z x then TVar y else sigma z.

Fixpoint substitute (sigma : nat -> term) (t : term) : term :=
  match t with
  | TVar n => sigma n
  | TSort k => TSort k
  | TPi x A B => let y := substitution_binder sigma x B in
      TPi y (substitute sigma A) (substitute (bind_substitution sigma x y) B)
  | TLam x b => let y := substitution_binder sigma x b in
      TLam y (substitute (bind_substitution sigma x y) b)
  | TApp f a => TApp (substitute sigma f) (substitute sigma a)
  | TSigma x A B => let y := substitution_binder sigma x B in
      TSigma y (substitute sigma A) (substitute (bind_substitution sigma x y) B)
  | TPair a b => TPair (substitute sigma a) (substitute sigma b)
  | TFst p => TFst (substitute sigma p)
  | TSnd p => TSnd (substitute sigma p)
  | TUnitT  => TUnitT
  | TUnit  => TUnit
  | TUId  => TUId
  | TTag s => TTag s
  | TEnumU  => TEnumU
  | TNilE  => TNilE
  | TConsE tag E => TConsE (substitute sigma tag) (substitute sigma E)
  | TEnumT E => TEnumT (substitute sigma E)
  | TEZero  => TEZero
  | TESucc n => TESucc (substitute sigma n)
  | TEPi k E P => TEPi k (substitute sigma E) (substitute sigma P)
  | TSwitch k E P p e => TSwitch k (substitute sigma E) (substitute sigma P) (substitute sigma p) (substitute sigma e)
  | TIDesc IT => TIDesc (substitute sigma IT)
  | TIVar i => TIVar (substitute sigma i)
  | TI1  => TI1
  | TIBot  => TIBot
  | TIProd A B => TIProd (substitute sigma A) (substitute sigma B)
  | TIPi A D => TIPi (substitute sigma A) (substitute sigma D)
  | TISig A D => TISig (substitute sigma A) (substitute sigma D)
  | TIChoice E D => TIChoice (substitute sigma E) (substitute sigma D)
  | TInterp IT D X => TInterp (substitute sigma IT) (substitute sigma D) (substitute sigma X)
  | TMuI IT D => TMuI (substitute sigma IT) (substitute sigma D)
  | TIn x => TIn (substitute sigma x)
  | TInd IT D P s i x => TInd (substitute sigma IT) (substitute sigma D) (substitute sigma P) (substitute sigma s) (substitute sigma i) (substitute sigma x)
  | TIAll IT D X x P => TIAll (substitute sigma IT) (substitute sigma D) (substitute sigma X) (substitute sigma x) (substitute sigma P)
  | THyps IT D X P h x => THyps (substitute sigma IT) (substitute sigma D) (substitute sigma X) (substitute sigma P) (substitute sigma h) (substitute sigma x)
  | TClose IT F G => TClose (substitute sigma IT) (substitute sigma F) (substitute sigma G)
  | TCloseCase k IT F G i Q b x => TCloseCase k (substitute sigma IT) (substitute sigma F) (substitute sigma G) (substitute sigma i) (substitute sigma Q) (substitute sigma b) (substitute sigma x)
  | TCloseInd IT G P s F i x => TCloseInd (substitute sigma IT) (substitute sigma G) (substitute sigma P) (substitute sigma s) (substitute sigma F) (substitute sigma i) (substitute sigma x)
  end.

Definition subst (u : term) (x : nat) (t : term) : term :=
  substitute (fun y => if Nat.eqb y x then u else TVar y) t.

(* A finite map from stable binding IDs to types. Types and ordinary terms
   share syntax, so dependent types can refer to ordinary term bindings. *)
Module VarMap := FMapAVL.Make(Nat_as_OT).
Definition ctx := VarMap.t term.
Definition empty_ctx : ctx := VarMap.empty term.
Definition lookup (Gamma : ctx) (x : nat) := VarMap.find x Gamma.
Definition extend (Gamma : ctx) (x : nat) (A : term) := VarMap.add x A Gamma.
Definition fresh_in (Gamma : ctx) (x : nat) := lookup Gamma x = None.

(* One-layer compatible closure, used only for definitional congruence.
   R relates each pair of corresponding subterms, including under binders. *)
Inductive compatible (R : term -> term -> Prop) : term -> term -> Prop :=
| cp_TVar : forall n, compatible R (TVar n) (TVar n)
| cp_TSort : forall k, compatible R (TSort k) (TSort k)
| cp_TPi : forall x A A' B B', R A A' -> R B B' -> compatible R (TPi x A B) (TPi x A' B')
| cp_TLam : forall x b b', R b b' -> compatible R (TLam x b) (TLam x b')
| cp_TApp : forall f f' a a', R f f' -> R a a' -> compatible R (TApp f a) (TApp f' a')
| cp_TSigma : forall x A A' B B', R A A' -> R B B' -> compatible R (TSigma x A B) (TSigma x A' B')
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

Definition identity := TLam 0 (TVar 0).
Definition constant (t : term) := TLam (fresh [t]) t.
Definition arrow (A B : term) := TPi (fresh [A; B]) A B.
Definition product (A B : term) := TSigma (fresh [A; B]) A B.
Definition Def (IT : term) := TPi (fresh [IT]) IT (TIDesc IT).
Definition Family (IT : term) := TPi (fresh [IT]) IT (TSort 0).
Definition Bot := TEnumT TNilE.
Definition CloseAt IT F G i := TApp (TClose IT F G) i.
Definition MuAt IT D i := TApp (TMuI IT D) i.
Definition carrier IT G := TClose IT G G.
Definition payload IT F G i := TInterp IT (TApp F i) (carrier IT G).
Definition total IT X :=
  let i := fresh [IT; X] in TSigma i IT (TApp X (TVar i)).
Definition motive IT X := arrow (total IT X) (TSort 0).
Definition recursive_method IT X P :=
  let i := fresh [IT; X; P] in let x := S i in
  TPi i IT (TPi x (TApp X (TVar i)) (TApp P (TPair (TVar i) (TVar x)))).
Definition abort (k : nat) (A z : term) :=
  TSwitch k TNilE (constant A) TUnit z.
Definition close_case_method IT F G i Q :=
  let x := fresh [IT; F; G; i; Q] in
  TPi x (payload IT F G i) (TApp Q (TIn (TVar x))).
Definition unroll IT F G i x :=
  TCloseCase 0 IT F G i (constant (payload IT F G i)) identity x.

Definition close_motive IT G :=
  let f := fresh [IT; G] in let i := S f in let x := S i in
  TPi f (Def IT) (TPi i IT
    (TPi x (CloseAt IT (TVar f) G (TVar i)) (TSort 0))).
Definition diagonal_motive G P :=
  let x := fresh [G; P] in
  TLam x (TApp (TApp (TApp P G) (TFst (TVar x))) (TSnd (TVar x))).
Definition close_ind_method IT G P :=
  let f := fresh [IT; G; P] in let i := S f in
  let x := S i in let h := S x in
  TPi f (Def IT) (TPi i IT
    (TPi x (payload IT (TVar f) G (TVar i))
      (TPi h (TIAll IT (TApp (TVar f) (TVar i)) (carrier IT G)
        (TVar x) (diagonal_motive G P))
        (TApp (TApp (TApp P (TVar f)) (TVar i)) (TIn (TVar x)))))).
Definition mu_ind_method IT D P :=
  let i := fresh [IT; D; P] in let x := S i in let h := S x in
  TPi i IT
    (TPi x (TInterp IT (TApp D (TVar i)) (TMuI IT D))
      (TPi h (TIAll IT (TApp D (TVar i)) (TMuI IT D) (TVar x) P)
        (TApp P (TPair (TVar i) (TIn (TVar x)))))).

(* x is the source Pi binder, y is the target Pi binder. *)
Definition coerced_codomain (x y : nat) c B := subst (TApp c (TVar y)) x B.
Definition compose_coercion c d :=
  let x := fresh [c; d] in TLam x (TApp d (TApp c (TVar x))).
Definition pi_coercion (y : nat) c d :=
  let f := fresh [c; d; TVar y] in
  TLam f (TLam y (TApp d (TApp (TVar f) (TApp c (TVar y))))).
Definition close_coercion (IT F H G i q : term) :=
  let x := fresh [IT; F; H; G; i; q] in
  TLam x (TIn (TApp q (unroll IT F G i (TVar x)))).

Fixpoint enum_position (n : nat) : term :=
  match n with 0 => TEZero | S n => TESucc (enum_position n) end.
Fixpoint tuple (ts : list term) : term :=
  match ts with [] => TUnit | t :: ts => TPair t (tuple ts) end.
