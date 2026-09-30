(* Auxiliary regular typing: explicit result formations support reflection. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export nameless.DBConfluence.
Import ListNotations.

Inductive wf : ctx -> Prop :=
| wf_nil : wf []
| wf_cons : forall Gamma A k,
    wf Gamma -> typing Gamma A (TSort k) -> wf (A :: Gamma)
with typing : ctx -> term -> term -> Prop :=
| ty_var : forall Gamma (formation_level : nat) n A,
    wf Gamma -> nth_error Gamma n = Some A ->
    typing Gamma (lift (S n) 0 A) (TSort formation_level) ->
    typing Gamma (TVar n) (lift (S n) 0 A)
| ty_sort : forall Gamma k,
    wf Gamma -> typing Gamma (TSort k) (TSort (S k))
| ty_pi : forall Gamma A B j k,
    typing Gamma A (TSort j) -> typing (A :: Gamma) B (TSort k) ->
    typing Gamma (TPi A B) (TSort (Nat.max j k))
| ty_sigma : forall Gamma A B j k,
    typing Gamma A (TSort j) -> typing (A :: Gamma) B (TSort k) ->
    typing Gamma (TSigma A B) (TSort (Nat.max j k))
| ty_lam : forall Gamma A B b k,
    typing Gamma (TPi A B) (TSort k) -> typing (A :: Gamma) b B ->
    typing Gamma (TLam b) (TPi A B)
| ty_app : forall Gamma (formation_level : nat) A B f a k,
    typing Gamma (TPi A B) (TSort k) ->
    typing Gamma f (TPi A B) -> typing Gamma a A ->
    typing Gamma (subst a 0 B) (TSort formation_level) ->
    typing Gamma (TApp f a) (subst a 0 B)
| ty_pair : forall Gamma A B a b k,
    typing Gamma (TSigma A B) (TSort k) ->
    typing Gamma a A -> typing Gamma b (subst a 0 B) ->
    typing Gamma (TPair a b) (TSigma A B)
| ty_fst : forall Gamma (formation_level : nat) A B p k,
    typing Gamma (TSigma A B) (TSort k) ->
    typing Gamma p (TSigma A B) -> typing Gamma A (TSort formation_level) ->
    typing Gamma (TFst p) A
| ty_snd : forall Gamma (formation_level : nat) A B p k,
    typing Gamma (TSigma A B) (TSort k) ->
    typing Gamma p (TSigma A B) ->
    typing Gamma (subst (TFst p) 0 B) (TSort formation_level) ->
    typing Gamma (TSnd p) (subst (TFst p) 0 B)
| ty_conv : forall Gamma t A B k,
    typing Gamma t A -> typing Gamma B (TSort k) -> conv A B ->
    typing Gamma t B
| ty_cumul : forall Gamma t j k,
    typing Gamma t (TSort j) -> j <= k -> typing Gamma t (TSort k)
| ty_unitT : forall Gamma k, wf Gamma -> typing Gamma TUnitT (TSort k)
| ty_unit : forall Gamma (formation_level : nat), wf Gamma -> typing Gamma TUnitT (TSort formation_level) ->
    typing Gamma TUnit TUnitT
| ty_uid : forall Gamma, wf Gamma -> typing Gamma TUId (TSort 0)
| ty_tag : forall Gamma (formation_level : nat) s, wf Gamma -> typing Gamma TUId (TSort formation_level) ->
    typing Gamma (TTag s) TUId
| ty_enumu : forall Gamma, wf Gamma -> typing Gamma TEnumU (TSort 0)
| ty_nile : forall Gamma (formation_level : nat), wf Gamma -> typing Gamma TEnumU (TSort formation_level) ->
    typing Gamma TNilE TEnumU
| ty_conse : forall Gamma (formation_level : nat) tag E,
    typing Gamma tag TUId -> typing Gamma E TEnumU ->
    typing Gamma TEnumU (TSort formation_level) ->
    typing Gamma (TConsE tag E) TEnumU
| ty_enumt : forall Gamma E,
    typing Gamma E TEnumU -> typing Gamma (TEnumT E) (TSort 0)
| ty_zero : forall Gamma (formation_level : nat) tag E,
    typing Gamma tag TUId -> typing Gamma E TEnumU ->
    typing Gamma (TEnumT (TConsE tag E)) (TSort formation_level) ->
    typing Gamma TEZero (TEnumT (TConsE tag E))
| ty_succ : forall Gamma (formation_level : nat) tag E n,
    typing Gamma tag TUId -> typing Gamma E TEnumU ->
    typing Gamma n (TEnumT E) ->
    typing Gamma (TEnumT (TConsE tag E)) (TSort formation_level) ->
    typing Gamma (TESucc n) (TEnumT (TConsE tag E))
| ty_epi : forall Gamma k E P,
    typing Gamma E TEnumU ->
    typing Gamma P (TPi (TEnumT E) (TSort k)) ->
    typing Gamma (TEPi k E P) (TSort k)
| ty_switch : forall Gamma (formation_level : nat) k E P p e,
    typing Gamma E TEnumU ->
    typing Gamma P (TPi (TEnumT E) (TSort k)) ->
    typing Gamma p (TEPi k E P) -> typing Gamma e (TEnumT E) ->
    typing Gamma (TApp P e) (TSort formation_level) ->
    typing Gamma (TSwitch k E P p e) (TApp P e)
| ty_idesc : forall Gamma IT,
    typing Gamma IT (TSort 0) -> typing Gamma (TIDesc IT) (TSort 1)
| ty_ivar : forall Gamma (formation_level : nat) IT i,
    typing Gamma IT (TSort 0) -> typing Gamma i IT ->
    typing Gamma (TIDesc IT) (TSort formation_level) ->
    typing Gamma (TIVar i) (TIDesc IT)
| ty_i1 : forall Gamma (formation_level : nat) IT,
    typing Gamma IT (TSort 0) -> typing Gamma (TIDesc IT) (TSort formation_level) ->
    typing Gamma TI1 (TIDesc IT)
| ty_ibot : forall Gamma (formation_level : nat) IT,
    typing Gamma IT (TSort 0) -> typing Gamma (TIDesc IT) (TSort formation_level) ->
    typing Gamma TIBot (TIDesc IT)
| ty_iprod : forall Gamma (formation_level : nat) IT A B,
    typing Gamma IT (TSort 0) ->
    typing Gamma A (TIDesc IT) -> typing Gamma B (TIDesc IT) ->
    typing Gamma (TIDesc IT) (TSort formation_level) ->
    typing Gamma (TIProd A B) (TIDesc IT)
| ty_ipi : forall Gamma (formation_level : nat) IT A D,
    typing Gamma IT (TSort 0) -> typing Gamma A (TSort 0) ->
    typing Gamma D (arrow A (TIDesc IT)) ->
    typing Gamma (TIDesc IT) (TSort formation_level) ->
    typing Gamma (TIPi A D) (TIDesc IT)
| ty_isig : forall Gamma (formation_level : nat) IT A D,
    typing Gamma IT (TSort 0) -> typing Gamma A (TSort 0) ->
    typing Gamma D (arrow A (TIDesc IT)) ->
    typing Gamma (TIDesc IT) (TSort formation_level) ->
    typing Gamma (TISig A D) (TIDesc IT)
| ty_ichoice : forall Gamma (formation_level : nat) IT E D,
    typing Gamma IT (TSort 0) -> typing Gamma E TEnumU ->
    typing Gamma D (arrow (TEnumT E) (TIDesc IT)) ->
    typing Gamma (TIDesc IT) (TSort formation_level) ->
    typing Gamma (TIChoice E D) (TIDesc IT)
| ty_interp : forall Gamma IT D X,
    typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) ->
    typing Gamma X (Family IT) ->
    typing Gamma (TInterp IT D X) (TSort 0)
| ty_mui : forall Gamma (formation_level : nat) IT D,
    typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
    typing Gamma (Family IT) (TSort formation_level) ->
    typing Gamma (TMuI IT D) (Family IT)
| ty_in_mui : forall Gamma (formation_level : nat) IT D i xs,
    typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
    typing Gamma i IT -> typing Gamma xs (TInterp IT (TApp D i) (TMuI IT D)) ->
    typing Gamma (MuAt IT D i) (TSort formation_level) ->
    typing Gamma (TIn xs) (MuAt IT D i)
| ty_iall : forall Gamma IT D X xs P,
    typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) ->
    typing Gamma X (Family IT) -> typing Gamma xs (TInterp IT D X) ->
    typing Gamma P (motive IT X) ->
    typing Gamma (TIAll IT D X xs P) (TSort 0)
| ty_hyps : forall Gamma (formation_level : nat) IT D X P h xs,
    typing Gamma IT (TSort 0) -> typing Gamma D (TIDesc IT) ->
    typing Gamma X (Family IT) -> typing Gamma P (motive IT X) ->
    typing Gamma h (recursive_method IT X P) ->
    typing Gamma xs (TInterp IT D X) ->
    typing Gamma (TIAll IT D X xs P) (TSort formation_level) ->
    typing Gamma (THyps IT D X P h xs) (TIAll IT D X xs P)
| ty_ind : forall Gamma (formation_level : nat) IT D P st i x,
    typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) ->
    typing Gamma P (motive IT (TMuI IT D)) ->
    typing Gamma st (mu_ind_method IT D P) ->
    typing Gamma i IT -> typing Gamma x (MuAt IT D i) ->
    typing Gamma (TApp P (TPair i x)) (TSort formation_level) ->
    typing Gamma (TInd IT D P st i x) (TApp P (TPair i x))
| ty_close : forall Gamma (formation_level : nat) IT F G,
    typing Gamma IT (TSort 0) ->
    typing Gamma F (Def IT) -> typing Gamma G (Def IT) ->
    typing Gamma (Family IT) (TSort formation_level) ->
    typing Gamma (TClose IT F G) (Family IT)
| ty_in_close : forall Gamma (formation_level : nat) IT F G i xs,
    typing Gamma IT (TSort 0) ->
    typing Gamma F (Def IT) -> typing Gamma G (Def IT) ->
    typing Gamma i IT -> typing Gamma xs (payload IT F G i) ->
    typing Gamma (CloseAt IT F G i) (TSort formation_level) ->
    typing Gamma (TIn xs) (CloseAt IT F G i)
| ty_close_case : forall Gamma (formation_level : nat) k IT F G i Q b x,
    typing Gamma IT (TSort 0) ->
    typing Gamma F (Def IT) -> typing Gamma G (Def IT) ->
    typing Gamma i IT ->
    typing Gamma Q (TPi (CloseAt IT F G i) (TSort k)) ->
    typing Gamma b (close_case_method IT F G i Q) ->
    typing Gamma x (CloseAt IT F G i) ->
    typing Gamma (TApp Q x) (TSort formation_level) ->
    typing Gamma (TCloseCase k IT F G i Q b x) (TApp Q x)
| ty_close_ind : forall Gamma (formation_level : nat) IT G P st F i x,
    typing Gamma IT (TSort 0) -> typing Gamma G (Def IT) ->
    typing Gamma P (close_motive IT G) ->
    typing Gamma st (close_ind_method IT G P) ->
    typing Gamma F (Def IT) -> typing Gamma i IT ->
    typing Gamma x (CloseAt IT F G i) ->
    typing Gamma (TApp (TApp (TApp P F) i) x) (TSort formation_level) ->
    typing Gamma (TCloseInd IT G P st F i x)
      (TApp (TApp (TApp P F) i) x).

Definition type_wf Gamma A := exists k, typing Gamma A (TSort k).
