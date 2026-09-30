(* Relational elaboration for open signatures.
   Constructor identities are strings, while core tags are local positions.
   Source payload schemes below are already positive description expressions:
   the surface recursive binder is represented by TIVar, not arbitrary
   negative Set-valued recursion. This is not a parser or a deciding checker. *)
From Stdlib Require Import List Arith String.
Require Export OpenSignaturesCore.
Import ListNotations.
Set Implicit Arguments.

Definition row := list (string * term).
Fixpoint row_enum (rs : row) : term :=
  match rs with
  | [] => TNilE
  | (name, _) :: rs => TConsE (TTag name) (row_enum rs)
  end.
Definition row_names (rs : row) := map fst rs.
Definition row_tuple (rs : row) := tuple (map snd rs).
Definition row_branches IT (rs : row) :=
  let e := fresh (IT :: map snd rs) in
  let m := S e in
  TLam e (TSwitch 1 (row_enum rs)
    (TLam m (TIDesc IT)) (row_tuple rs) (TVar e)).
Definition row_code IT rs := TIChoice (row_enum rs) (row_branches IT rs).

(* rs is scoped under the index binder i:IT. *)
Definition signature (i : nat) IT rs := TLam i (row_code IT rs).

Definition row_input Gamma IT rs :=
  typing Gamma IT (TSort 0) /\ NoDup (row_names rs) /\
  Forall (fun entry => typing Gamma (snd entry) (TIDesc IT)) rs.

Inductive row_view (Gamma : ctx) (IT D : term) : row -> Prop :=
| view_rows : forall rs,
    row_input Gamma IT rs -> typing Gamma D (TIDesc IT) ->
    conv D (row_code IT rs) -> row_view Gamma IT D rs.

(* Motive of a switch selecting functions from branch payloads into Y. *)
Definition handler_motive IT rs X Y :=
  let branches := row_branches IT rs in
  let e := fresh [IT; branches; X; Y] in
  let p := S e in
  TLam e (TPi p (TInterp IT (TApp branches (TVar e)) X) Y).
Definition row_map (k : nat) IT rs X Y handlers :=
  let P := handler_motive IT rs X Y in
  let hs := tuple handlers in
  let p := fresh [IT; row_tuple rs; X; Y; P; hs] in
  TLam p (TApp
    (TSwitch k (row_enum rs) P hs (TFst (TVar p))) (TSnd (TVar p))).
Definition retag_handler (n : nat) :=
  let p := fresh [enum_position n] in
  TLam p (TPair (enum_position n) (TVar p)).
Definition dead_handler (k : nat) Y d :=
  let p := fresh [Y; d] in
  TLam p (abort k Y (TApp d (TVar p))).
Definition identity_for (ts : list term) :=
  let x := fresh ts in TLam x (TVar x).

(* Success carries an actual function from the source payload to Bot.
   The provided-witness rule checks an explicit term; it is not an oracle
   asserting semantic emptiness and supplies no search algorithm. *)
Inductive dead : ctx -> term -> term -> term -> term -> Prop :=
| dead_bot : forall Gamma IT D X,
    description_input Gamma IT D X -> conv D TIBot ->
    dead Gamma IT D X (identity_for [IT; D; X])
| dead_nil : forall Gamma IT D X T,
    description_input Gamma IT D X -> conv D (TIChoice TNilE T) ->
    dead Gamma IT D X
      (let x := fresh [IT; D; X; T] in TLam x (TFst (TVar x)))
| dead_left : forall Gamma IT D X A B d,
    description_input Gamma IT D X -> conv D (TIProd A B) ->
    dead Gamma IT A X d ->
    dead Gamma IT D X
      (let x := fresh [IT; D; X; A; B; d] in
       TLam x (TApp d (TFst (TVar x))))
| dead_right : forall Gamma IT D X A B d,
    description_input Gamma IT D X -> conv D (TIProd A B) ->
    dead Gamma IT B X d ->
    dead Gamma IT D X
      (let x := fresh [IT; D; X; A; B; d] in
       TLam x (TApp d (TSnd (TVar x))))
| dead_choice : forall Gamma IT D X rs handlers,
    description_input Gamma IT D X -> row_view Gamma IT D rs ->
    dead_rows Gamma IT rs X handlers ->
    dead Gamma IT D X (row_map 0 IT rs X Bot handlers)
| dead_provided : forall Gamma IT D X d,
    description_input Gamma IT D X ->
    typing Gamma d (arrow (TInterp IT D X) Bot) ->
    dead Gamma IT D X d
with dead_rows : ctx -> term -> row -> term -> list term -> Prop :=
| dr_nil : forall Gamma IT X, dead_rows Gamma IT [] X []
| dr_cons : forall Gamma IT X name D rs d ds,
    dead Gamma IT D X d -> dead_rows Gamma IT rs X ds ->
    dead_rows Gamma IT ((name,D) :: rs) X (d :: ds).

(* No mapping is needed for an impossible source label, even when the target
   does not contain its identity. Live mappings preserve the payload. *)
Inductive row_handlers
    (Gamma : ctx) (IT X Y : term) (target : row)
    : row -> list term -> Prop :=
| rh_nil : row_handlers Gamma IT X Y target [] []
| rh_live : forall name D rs D' n hs,
    nth_error target n = Some (name,D') ->
    conv (TInterp IT D X) (TInterp IT D' X) ->
    row_handlers Gamma IT X Y target rs hs ->
    row_handlers Gamma IT X Y target ((name,D) :: rs)
      (retag_handler n :: hs)
| rh_dead : forall name D rs d hs,
    dead Gamma IT D X d ->
    row_handlers Gamma IT X Y target rs hs ->
    row_handlers Gamma IT X Y target ((name,D) :: rs)
      (dead_handler 0 Y d :: hs).

Inductive desc_sub : ctx -> term -> term -> term -> term -> term -> Prop :=
| ds_conv : forall Gamma IT D D' X,
    description_input Gamma IT D X ->
    description_input Gamma IT D' X -> conv D D' ->
    desc_sub Gamma IT D D' X (identity_for [IT; D; D'; X])
| ds_dead : forall Gamma IT D D' X d,
    dead Gamma IT D X d -> description_input Gamma IT D' X ->
    desc_sub Gamma IT D D' X (dead_handler 0 (TInterp IT D' X) d)
| ds_rows : forall Gamma IT D D' X rs rt handlers,
    description_input Gamma IT D X -> description_input Gamma IT D' X ->
    row_view Gamma IT D rs -> row_view Gamma IT D' rt ->
    row_handlers Gamma IT X (TInterp IT D' X) rt rs handlers ->
    desc_sub Gamma IT D D' X
      (row_map 0 IT rs X (TInterp IT D' X) handlers).

Inductive sub : ctx -> term -> term -> term -> Prop :=
| su_conv : forall Gamma A B,
    type_wf Gamma A -> type_wf Gamma B -> conv A B ->
    sub Gamma A B (identity_for [A; B])
| su_trans : forall Gamma A B C c d,
    sub Gamma A B c -> sub Gamma B C d ->
    sub Gamma A C (compose_coercion c d)
| su_bottom : forall Gamma A k,
    typing Gamma A (TSort k) ->
    sub Gamma Bot A
      (let x := fresh [A] in TLam x (abort k A (TVar x)))
| su_pi : forall Gamma x y A B A' B' c d,
    fresh_in Gamma y ->
    type_wf Gamma (TPi x A B) -> type_wf Gamma (TPi y A' B') ->
    sub Gamma A' A c ->
    sub (extend Gamma y A') (coerced_codomain x y c B) B' d ->
    sub Gamma (TPi x A B) (TPi y A' B') (pi_coercion y c d)
| su_close : forall Gamma IT F H G i q,
    close_input Gamma IT F G i -> close_input Gamma IT H G i ->
    desc_sub Gamma IT (TApp F i) (TApp H i) (carrier IT G) q ->
    sub Gamma (CloseAt IT F G i) (CloseAt IT H G i)
      (close_coercion IT F H G i q).

(* A finite source language for the specified elaboration boundary.
   ECore is checked-only: EAnn must supply its type to synthesize. Allowing
   arbitrary declarative types to be guessed for raw In terms would give
   ambiguous constructor identities and invalidate elaboration coherence.
   ESignature's payload schemes
   are scoped under its index binder; a source recursive slot has already
   been translated to TIVar by the description grammar.
   Case clauses bind one payload variable; Q is nondependent source syntax.
   The core closeCase operator itself has a dependent motive. *)
Inductive expr : Type :=
| ECore (t : term)
| EVar (n : nat)
| EAnn (e : expr) (A : term)
| ELam (x : nat) (e : expr)
| EApp (f a : expr)
| EPair (a b : expr)
| ESignature (i : nat) (IT : term) (rs : row)
| EClose (IT : term) (F G : expr)
| EConstructor (name : string) (xs : expr)
| ECase (scrutinee : expr) (Q : term)
    (clauses : list (string * (nat * expr))).

Definition clause_names (bs : list (string * (nat * expr))) := map fst bs.
Definition case_term k IT F G i Q rs handlers x :=
  let b := row_map k IT rs (carrier IT G) Q handlers in
  let z := fresh [IT; F; G; i; Q; row_tuple rs; tuple handlers; x; b] in
  TCloseCase k IT F G i (TLam z Q) b x.

Inductive elab_synth : ctx -> expr -> term -> term -> Prop :=
| es_var : forall Gamma n A,
    wf Gamma -> lookup Gamma n = Some A ->
    elab_synth Gamma (EVar n) A (TVar n)
| es_ann : forall Gamma e A t,
    type_wf Gamma A -> elab_check Gamma e A t ->
    elab_synth Gamma (EAnn e A) A t
| es_app : forall Gamma x f a A B t u,
    type_wf Gamma (TPi x A B) ->
    elab_synth Gamma f (TPi x A B) t -> elab_check Gamma a A u ->
    elab_synth Gamma (EApp f a) (subst u x B) (TApp t u)
| es_signature : forall Gamma i IT rs,
    fresh_in Gamma i ->
    typing Gamma IT (TSort 0) ->
    row_input (extend Gamma i IT) IT rs ->
    elab_synth Gamma (ESignature i IT rs) (Def IT) (signature i IT rs)
| es_close : forall Gamma IT F G f g,
    typing Gamma IT (TSort 0) ->
    elab_check Gamma F (Def IT) f -> elab_check Gamma G (Def IT) g ->
    elab_synth Gamma (EClose IT F G) (Family IT) (TClose IT f g)
| es_case : forall Gamma e Q bs IT F G i x rs k hs,
    close_input Gamma IT F G i ->
    elab_synth Gamma e (CloseAt IT F G i) x ->
    typing Gamma Q (TSort k) ->
    row_view Gamma IT (TApp F i) rs ->
    NoDup (clause_names bs) ->
    Forall (fun entry => In (fst entry) (row_names rs)) bs ->
    elab_cases Gamma k IT (carrier IT G) Q bs rs hs ->
    elab_synth Gamma (ECase e Q bs) Q
      (case_term k IT F G i Q rs hs x)
with elab_check : ctx -> expr -> term -> term -> Prop :=
| ec_core : forall Gamma t A,
    typing Gamma t A -> elab_check Gamma (ECore t) A t
| ec_conversion : forall Gamma e A B t,
    elab_synth Gamma e A t -> type_wf Gamma B -> conv A B ->
    elab_check Gamma e B t
| ec_target_conversion : forall Gamma e A B t,
    elab_check Gamma e A t -> type_wf Gamma B -> conv A B ->
    elab_check Gamma e B t
| ec_subsumption : forall Gamma e A B t c,
    elab_synth Gamma e A t -> sub Gamma A B c ->
    elab_check Gamma e B (TApp c t)
| ec_lam : forall Gamma x e A B t,
    fresh_in Gamma x ->
    type_wf Gamma (TPi x A B) -> elab_check (extend Gamma x A) e B t ->
    elab_check Gamma (ELam x e) (TPi x A B) (TLam x t)
| ec_pair : forall Gamma x e f A B t u,
    type_wf Gamma (TSigma x A B) ->
    elab_check Gamma e A t -> elab_check Gamma f (subst t x B) u ->
    elab_check Gamma (EPair e f) (TSigma x A B) (TPair t u)
| ec_constructor : forall Gamma name e IT F G i rs n D xs,
    close_input Gamma IT F G i ->
    row_view Gamma IT (TApp F i) rs ->
    nth_error rs n = Some (name,D) ->
    elab_check Gamma e (TInterp IT D (carrier IT G)) xs ->
    elab_check Gamma (EConstructor name e) (CloseAt IT F G i)
      (TIn (TPair (enum_position n) xs))
with elab_cases :
    ctx -> nat -> term -> term -> term -> list (string * (nat * expr)) ->
    row -> list term -> Prop :=
| cases_nil : forall Gamma k IT X Q bs,
    elab_cases Gamma k IT X Q bs [] []
| cases_live : forall Gamma k IT X Q bs name D rs p e t hs,
    In (name,(p,e)) bs -> fresh_in Gamma p ->
    elab_check (extend Gamma p (TInterp IT D X)) e Q t ->
    elab_cases Gamma k IT X Q bs rs hs ->
    elab_cases Gamma k IT X Q bs ((name,D) :: rs) (TLam p t :: hs)
| cases_dead : forall Gamma k IT X Q bs name D rs d hs,
    ~ In name (clause_names bs) ->
    dead Gamma IT D X d ->
    elab_cases Gamma k IT X Q bs rs hs ->
    elab_cases Gamma k IT X Q bs ((name,D) :: rs)
      (dead_handler k Q d :: hs).
