(* Declarative checking of the annotated core.

   Annotations are recursive annotated terms and are checked by these rules.
   Context entries and judgment result types use their erased representation:
   annotations distinguish programs, not the conversion class of a type.
   The existing, independently checked raw conversion and universe comparison
   therefore remain usable. No reduction or preservation premise occurs here. *)
From Stdlib Require Import List Arith.
Require Export annotated.AErasure.
Require nameless.DBDerivedTyping.
Import ListNotations.
Module RT := nameless.DBTyping.
Module DT := nameless.DBDerivedTyping.

Inductive typing : Raw.ctx -> term -> Raw.term -> Prop :=
| ty_var : forall Gamma n A,
    RT.wf Gamma -> nth_error Gamma n = Some A ->
    typing Gamma (TVar n) (Raw.lift (S n) 0 A)
| ty_sort : forall Gamma k,
    RT.wf Gamma -> typing Gamma (TSort k) (Raw.TSort (S k))
| ty_pi : forall Gamma A B j k,
    typing Gamma A (Raw.TSort j) ->
    typing (erase A :: Gamma) B (Raw.TSort k) ->
    typing Gamma (TPi A B) (Raw.TSort (Nat.max j k))
| ty_sigma : forall Gamma A B j k,
    typing Gamma A (Raw.TSort j) ->
    typing (erase A :: Gamma) B (Raw.TSort k) ->
    typing Gamma (TSigma A B) (Raw.TSort (Nat.max j k))
| ty_lam : forall Gamma A B b j k,
    typing Gamma A (Raw.TSort j) ->
    typing (erase A :: Gamma) B (Raw.TSort k) ->
    typing (erase A :: Gamma) b (erase B) ->
    typing Gamma (TLam A B b) (Raw.TPi (erase A) (erase B))
| ty_app : forall Gamma A B f a j k,
    typing Gamma A (Raw.TSort j) ->
    typing (erase A :: Gamma) B (Raw.TSort k) ->
    typing Gamma f (Raw.TPi (erase A) (erase B)) ->
    typing Gamma a (erase A) ->
    typing Gamma (TApp A B f a) (Raw.subst (erase a) 0 (erase B))
| ty_pair : forall Gamma A B a b j k,
    typing Gamma A (Raw.TSort j) ->
    typing (erase A :: Gamma) B (Raw.TSort k) ->
    typing Gamma a (erase A) ->
    typing Gamma b (Raw.subst (erase a) 0 (erase B)) ->
    typing Gamma (TPair A B a b) (Raw.TSigma (erase A) (erase B))
| ty_fst : forall Gamma A B p j k,
    typing Gamma A (Raw.TSort j) ->
    typing (erase A :: Gamma) B (Raw.TSort k) ->
    typing Gamma p (Raw.TSigma (erase A) (erase B)) ->
    typing Gamma (TFst A B p) (erase A)
| ty_snd : forall Gamma A B p j k,
    typing Gamma A (Raw.TSort j) ->
    typing (erase A :: Gamma) B (Raw.TSort k) ->
    typing Gamma p (Raw.TSigma (erase A) (erase B)) ->
    typing Gamma (TSnd A B p)
      (Raw.subst (Raw.TFst (erase p)) 0 (erase B))
| ty_conv : forall Gamma t A B k,
    typing Gamma t A -> RT.typing Gamma B (Raw.TSort k) ->
    nameless.DBCore.conv A B -> typing Gamma t B
| ty_cumul : forall Gamma t j k,
    typing Gamma t (Raw.TSort j) -> j <= k ->
    typing Gamma t (Raw.TSort k)
| ty_cumul_fun : forall Gamma f A B C D j k,
    typing Gamma f (Raw.TPi A B) ->
    RT.typing Gamma (Raw.TPi A B) (Raw.TSort j) ->
    RT.typing Gamma (Raw.TPi C D) (Raw.TSort k) ->
    RT.universe_le C A -> RT.universe_le B D ->
    typing Gamma f (Raw.TPi C D)
| ty_unitT : forall Gamma,
    RT.wf Gamma -> typing Gamma TUnitT (Raw.TSort 0)
| ty_unit : forall Gamma,
    RT.wf Gamma -> typing Gamma TUnit Raw.TUnitT
| ty_uid : forall Gamma,
    RT.wf Gamma -> typing Gamma TUId (Raw.TSort 0)
| ty_tag : forall Gamma s,
    RT.wf Gamma -> typing Gamma (TTag s) Raw.TUId
| ty_enumu : forall Gamma,
    RT.wf Gamma -> typing Gamma TEnumU (Raw.TSort 0)
| ty_nile : forall Gamma,
    RT.wf Gamma -> typing Gamma TNilE Raw.TEnumU
| ty_conse : forall Gamma tag E,
    typing Gamma tag Raw.TUId -> typing Gamma E Raw.TEnumU ->
    typing Gamma (TConsE tag E) Raw.TEnumU
| ty_enumt : forall Gamma E,
    typing Gamma E Raw.TEnumU -> typing Gamma (TEnumT E) (Raw.TSort 0)
| ty_zero : forall Gamma tag E,
    typing Gamma tag Raw.TUId -> typing Gamma E Raw.TEnumU ->
    typing Gamma (TEZero tag E) (Raw.TEnumT (Raw.TConsE (erase tag) (erase E)))
| ty_succ : forall Gamma tag E n,
    typing Gamma tag Raw.TUId -> typing Gamma E Raw.TEnumU ->
    typing Gamma n (Raw.TEnumT (erase E)) ->
    typing Gamma (TESucc tag E n) (Raw.TEnumT (Raw.TConsE (erase tag) (erase E)))
| ty_epi : forall Gamma k E P,
    typing Gamma E Raw.TEnumU ->
    typing Gamma P (Raw.TPi (Raw.TEnumT (erase E)) (Raw.TSort k)) ->
    typing Gamma (TEPi k E P) (Raw.TSort k)
| ty_switch : forall Gamma k E P p e,
    typing Gamma E Raw.TEnumU ->
    typing Gamma P (Raw.TPi (Raw.TEnumT (erase E)) (Raw.TSort k)) ->
    typing Gamma p (Raw.TEPi k (erase E) (erase P)) ->
    typing Gamma e (Raw.TEnumT (erase E)) ->
    typing Gamma (TSwitch k E P p e) (Raw.TApp (erase P) (erase e))
| ty_idesc : forall Gamma IT,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma (TIDesc IT) (Raw.TSort 1)
| ty_ivar : forall Gamma IT i,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma i (erase IT) ->
    typing Gamma (TIVar IT i) (Raw.TIDesc (erase IT))
| ty_i1 : forall Gamma IT,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma (TI1 IT) (Raw.TIDesc (erase IT))
| ty_ibot : forall Gamma IT,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma (TIBot IT) (Raw.TIDesc (erase IT))
| ty_iprod : forall Gamma IT A B,
    typing Gamma IT (Raw.TSort 0) ->
    typing Gamma A (Raw.TIDesc (erase IT)) ->
    typing Gamma B (Raw.TIDesc (erase IT)) ->
    typing Gamma (TIProd IT A B) (Raw.TIDesc (erase IT))
| ty_ipi : forall Gamma IT A D,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma A (Raw.TSort 0) ->
    typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) ->
    typing Gamma (TIPi IT A D) (Raw.TIDesc (erase IT))
| ty_isig : forall Gamma IT A D,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma A (Raw.TSort 0) ->
    typing Gamma D (Raw.arrow (erase A) (Raw.TIDesc (erase IT))) ->
    typing Gamma (TISig IT A D) (Raw.TIDesc (erase IT))
| ty_ichoice : forall Gamma IT E D,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma E Raw.TEnumU ->
    typing Gamma D (Raw.arrow (Raw.TEnumT (erase E)) (Raw.TIDesc (erase IT))) ->
    typing Gamma (TIChoice IT E D) (Raw.TIDesc (erase IT))
| ty_interp : forall Gamma IT D X,
    typing Gamma IT (Raw.TSort 0) ->
    typing Gamma D (Raw.TIDesc (erase IT)) ->
    typing Gamma X (Raw.Family (erase IT)) ->
    typing Gamma (TInterp IT D X) (Raw.TSort 0)
| ty_mui : forall Gamma IT D,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
    typing Gamma (TMuI IT D) (Raw.Family (erase IT))
| ty_in_mui : forall Gamma IT D i xs,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
    typing Gamma i (erase IT) ->
    typing Gamma xs (Raw.TInterp (erase IT) (Raw.TApp (erase D) (erase i))
      (Raw.TMuI (erase IT) (erase D))) ->
    typing Gamma (TInMu IT D i xs) (Raw.MuAt (erase IT) (erase D) (erase i))
| ty_iall : forall Gamma IT D X xs P,
    typing Gamma IT (Raw.TSort 0) ->
    typing Gamma D (Raw.TIDesc (erase IT)) ->
    typing Gamma X (Raw.Family (erase IT)) ->
    typing Gamma xs (Raw.TInterp (erase IT) (erase D) (erase X)) ->
    typing Gamma P (Raw.motive (erase IT) (erase X)) ->
    typing Gamma (TIAll IT D X xs P) (Raw.TSort 0)
| ty_hyps : forall Gamma IT D X P h xs,
    typing Gamma IT (Raw.TSort 0) ->
    typing Gamma D (Raw.TIDesc (erase IT)) ->
    typing Gamma X (Raw.Family (erase IT)) ->
    typing Gamma P (Raw.motive (erase IT) (erase X)) ->
    typing Gamma h (Raw.recursive_method (erase IT) (erase X) (erase P)) ->
    typing Gamma xs (Raw.TInterp (erase IT) (erase D) (erase X)) ->
    typing Gamma (THyps IT D X P h xs)
      (Raw.TIAll (erase IT) (erase D) (erase X) (erase xs) (erase P))
| ty_ind : forall Gamma IT D P st i x,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma D (Raw.Def (erase IT)) ->
    typing Gamma P (Raw.motive (erase IT) (Raw.TMuI (erase IT) (erase D))) ->
    typing Gamma st (Raw.mu_ind_method (erase IT) (erase D) (erase P)) ->
    typing Gamma i (erase IT) -> typing Gamma x (Raw.MuAt (erase IT) (erase D) (erase i)) ->
    typing Gamma (TInd IT D P st i x) (Raw.TApp (erase P) (Raw.TPair (erase i) (erase x)))
| ty_close : forall Gamma IT F G,
    typing Gamma IT (Raw.TSort 0) ->
    typing Gamma F (Raw.Def (erase IT)) -> typing Gamma G (Raw.Def (erase IT)) ->
    typing Gamma (TClose IT F G) (Raw.Family (erase IT))
| ty_in_close : forall Gamma IT F G i xs,
    typing Gamma IT (Raw.TSort 0) ->
    typing Gamma F (Raw.Def (erase IT)) -> typing Gamma G (Raw.Def (erase IT)) ->
    typing Gamma i (erase IT) ->
    typing Gamma xs (Raw.payload (erase IT) (erase F) (erase G) (erase i)) ->
    typing Gamma (TInClose IT F G i xs)
      (Raw.CloseAt (erase IT) (erase F) (erase G) (erase i))
| ty_close_case : forall Gamma k IT F G i Q b x,
    typing Gamma IT (Raw.TSort 0) ->
    typing Gamma F (Raw.Def (erase IT)) -> typing Gamma G (Raw.Def (erase IT)) ->
    typing Gamma i (erase IT) ->
    typing Gamma Q (Raw.TPi (Raw.CloseAt (erase IT) (erase F) (erase G) (erase i)) (Raw.TSort k)) ->
    typing Gamma b (Raw.close_case_method (erase IT) (erase F) (erase G) (erase i) (erase Q)) ->
    typing Gamma x (Raw.CloseAt (erase IT) (erase F) (erase G) (erase i)) ->
    typing Gamma (TCloseCase k IT F G i Q b x) (Raw.TApp (erase Q) (erase x))
| ty_close_ind : forall Gamma IT G P st F i x,
    typing Gamma IT (Raw.TSort 0) -> typing Gamma G (Raw.Def (erase IT)) ->
    typing Gamma P (Raw.close_motive (erase IT) (erase G)) ->
    typing Gamma st (Raw.close_ind_method (erase IT) (erase G) (erase P)) ->
    typing Gamma F (Raw.Def (erase IT)) -> typing Gamma i (erase IT) ->
    typing Gamma x (Raw.CloseAt (erase IT) (erase F) (erase G) (erase i)) ->
    typing Gamma (TCloseInd IT G P st F i x)
      (Raw.TApp (Raw.TApp (Raw.TApp (erase P) (erase F)) (erase i)) (erase x)).

Theorem typing_erasure : forall Gamma t A,
  typing Gamma t A -> RT.typing Gamma (erase t) A.
Proof.
  intros Gamma t A H; induction H; cbn [erase] in *.
  all: try solve [eauto 4 using RT.ty_sort, RT.ty_pi, RT.ty_sigma, RT.ty_lam,
    RT.ty_pair, RT.ty_conv, RT.ty_cumul, RT.ty_cumul_fun, RT.ty_unitT,
    RT.ty_unit, RT.ty_uid, RT.ty_tag, RT.ty_enumu, RT.ty_nile, RT.ty_conse,
    RT.ty_enumt, RT.ty_zero, RT.ty_succ, RT.ty_epi, RT.ty_idesc, RT.ty_ivar,
    RT.ty_i1, RT.ty_ibot, RT.ty_iprod, RT.ty_ipi, RT.ty_isig, RT.ty_ichoice,
    RT.ty_interp, RT.ty_iall, DT.smart_var, DT.smart_app, DT.smart_fst,
    DT.smart_snd, DT.smart_switch, DT.smart_mui, DT.smart_in_mui,
    DT.smart_hyps, DT.smart_ind, DT.smart_close, DT.smart_in_close,
    DT.smart_close_case, DT.smart_close_ind].
  all: eauto 6 using RT.ty_conse, RT.ty_enumt, RT.ty_enumu, RT.ty_zero,
    RT.ty_succ, nameless.DBWeakening.typing_context.
  Unshelve. all: exact 0.
Qed.

Corollary typing_context : forall Gamma t A, typing Gamma t A -> RT.wf Gamma.
Proof.
  intros Gamma t A H.
  exact (nameless.DBWeakening.typing_context _ _ _ (typing_erasure _ _ _ H)).
Qed.

Corollary type_correctness : forall Gamma t A, typing Gamma t A ->
  exists k, RT.typing Gamma A (Raw.TSort k).
Proof.
  intros Gamma t A H.
  exact (nameless.DBWeakening.type_correctness _ _ _ (typing_erasure _ _ _ H)).
Qed.

Print Assumptions typing_erasure.
Print Assumptions type_correctness.
