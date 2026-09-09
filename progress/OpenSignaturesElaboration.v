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
  TLam (TSwitch 1 (row_enum rs)
    (TLam (TIDesc (lift 2 0 IT))) (lift 1 0 (row_tuple rs)) (TVar 0)).
Definition row_code IT rs := TIChoice (row_enum rs) (row_branches IT rs).

(* rs is scoped under the index binder i:IT. *)
Definition signature IT rs := TLam (row_code (lift 1 0 IT) rs).

Definition row_input Gamma IT rs :=
  typing Gamma IT (TSort 0) /\ NoDup (row_names rs) /\
  Forall (fun entry => typing Gamma (snd entry) (TIDesc IT)) rs.

Inductive row_view (Gamma : ctx) (IT D : term) : row -> Prop :=
| view_rows : forall rs,
    row_input Gamma IT rs -> typing Gamma D (TIDesc IT) ->
    conv D (row_code IT rs) -> row_view Gamma IT D rs.

(* Motive of a switch selecting functions from branch payloads into Y. *)
Definition handler_motive IT rs X Y :=
  TLam (TPi
    (TInterp (lift 1 0 IT)
      (TApp (lift 1 0 (row_branches IT rs)) (TVar 0)) (lift 1 0 X))
    (lift 2 0 Y)).
Definition row_map (k : nat) IT rs X Y handlers :=
  TLam (TApp
    (TSwitch k (row_enum rs) (lift 1 0 (handler_motive IT rs X Y))
      (lift 1 0 (tuple handlers)) (TFst (TVar 0)))
    (TSnd (TVar 0))).
Definition retag_handler (n : nat) :=
  TLam (TPair (enum_position n) (TVar 0)).
Definition dead_handler (k : nat) Y d :=
  TLam (abort k (lift 1 0 Y) (TApp (lift 1 0 d) (TVar 0))).

(* Success carries an actual function from the source payload to Bot.
   The provided-witness rule checks an explicit term; it is not an oracle
   asserting semantic emptiness and supplies no search algorithm. *)
Inductive dead : ctx -> term -> term -> term -> term -> Prop :=
| dead_bot : forall Gamma IT D X,
    description_input Gamma IT D X -> conv D TIBot ->
    dead Gamma IT D X (TLam (TVar 0))
| dead_nil : forall Gamma IT D X T,
    description_input Gamma IT D X -> conv D (TIChoice TNilE T) ->
    dead Gamma IT D X (TLam (TFst (TVar 0)))
| dead_left : forall Gamma IT D X A B d,
    description_input Gamma IT D X -> conv D (TIProd A B) ->
    dead Gamma IT A X d ->
    dead Gamma IT D X (TLam (TApp (lift 1 0 d) (TFst (TVar 0))))
| dead_right : forall Gamma IT D X A B d,
    description_input Gamma IT D X -> conv D (TIProd A B) ->
    dead Gamma IT B X d ->
    dead Gamma IT D X (TLam (TApp (lift 1 0 d) (TSnd (TVar 0))))
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
    desc_sub Gamma IT D D' X (TLam (TVar 0))
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
    sub Gamma A B (TLam (TVar 0))
| su_trans : forall Gamma A B C c d,
    sub Gamma A B c -> sub Gamma B C d ->
    sub Gamma A C (compose_coercion c d)
| su_bottom : forall Gamma A k,
    typing Gamma A (TSort k) ->
    sub Gamma Bot A (TLam (abort k (lift 1 0 A) (TVar 0)))
| su_pi : forall Gamma A B A' B' c d,
    type_wf Gamma (TPi A B) -> type_wf Gamma (TPi A' B') ->
    sub Gamma A' A c ->
    sub (A' :: Gamma) (coerced_codomain c B) B' d ->
    sub Gamma (TPi A B) (TPi A' B') (pi_coercion c d)
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
| ELam (e : expr)
| EApp (f a : expr)
| EPair (a b : expr)
| ESignature (IT : term) (rs : row)
| EClose (IT : term) (F G : expr)
| EConstructor (name : string) (xs : expr)
| ECase (scrutinee : expr) (Q : term) (clauses : list (string * expr)).

Definition clause_names (bs : list (string * expr)) := map fst bs.
Definition case_term k IT F G i Q rs handlers x :=
  TCloseCase k IT F G i (TLam (lift 1 0 Q))
    (row_map k IT rs (carrier IT G) Q handlers) x.

Inductive elab_synth : ctx -> expr -> term -> term -> Prop :=
| es_var : forall Gamma n A,
    wf Gamma -> nth_error Gamma n = Some A ->
    elab_synth Gamma (EVar n) (lift (S n) 0 A) (TVar n)
| es_ann : forall Gamma e A t,
    type_wf Gamma A -> elab_check Gamma e A t ->
    elab_synth Gamma (EAnn e A) A t
| es_app : forall Gamma f a A B t u,
    type_wf Gamma (TPi A B) ->
    elab_synth Gamma f (TPi A B) t -> elab_check Gamma a A u ->
    elab_synth Gamma (EApp f a) (subst u 0 B) (TApp t u)
| es_signature : forall Gamma IT rs,
    typing Gamma IT (TSort 0) ->
    row_input (IT :: Gamma) (lift 1 0 IT) rs ->
    elab_synth Gamma (ESignature IT rs) (Def IT) (signature IT rs)
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
| ec_lam : forall Gamma e A B t,
    type_wf Gamma (TPi A B) -> elab_check (A :: Gamma) e B t ->
    elab_check Gamma (ELam e) (TPi A B) (TLam t)
| ec_pair : forall Gamma e f A B t u,
    type_wf Gamma (TSigma A B) ->
    elab_check Gamma e A t -> elab_check Gamma f (subst t 0 B) u ->
    elab_check Gamma (EPair e f) (TSigma A B) (TPair t u)
| ec_constructor : forall Gamma name e IT F G i rs n D xs,
    close_input Gamma IT F G i ->
    row_view Gamma IT (TApp F i) rs ->
    nth_error rs n = Some (name,D) ->
    elab_check Gamma e (TInterp IT D (carrier IT G)) xs ->
    elab_check Gamma (EConstructor name e) (CloseAt IT F G i)
      (TIn (TPair (enum_position n) xs))
with elab_cases :
    ctx -> nat -> term -> term -> term -> list (string * expr) ->
    row -> list term -> Prop :=
| cases_nil : forall Gamma k IT X Q bs,
    elab_cases Gamma k IT X Q bs [] []
| cases_live : forall Gamma k IT X Q bs name D rs e t hs,
    In (name,e) bs ->
    elab_check (TInterp IT D X :: Gamma) e (lift 1 0 Q) t ->
    elab_cases Gamma k IT X Q bs rs hs ->
    elab_cases Gamma k IT X Q bs ((name,D) :: rs) (TLam t :: hs)
| cases_dead : forall Gamma k IT X Q bs name D rs d hs,
    ~ In name (clause_names bs) ->
    dead Gamma IT D X d ->
    elab_cases Gamma k IT X Q bs rs hs ->
    elab_cases Gamma k IT X Q bs ((name,D) :: rs)
      (dead_handler k Q d :: hs).
