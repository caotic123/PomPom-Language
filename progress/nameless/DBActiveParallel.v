(* Parallel computation records whether a computational root is contracted.
   Keeping this bit through eta postponement rules out silent stuttering in
   the normalization transfer. The unmarked relation is unchanged. *)
From Stdlib Require Import Bool Lia.
Require Export nameless.DBEtaPostponement.

Inductive apstep : bool -> term -> term -> Prop :=
| aps_TVar : forall n, apstep false (TVar n) (TVar n)
| aps_TSort : forall k, apstep false (TSort k) (TSort k)
| aps_TPi : forall (a0 : bool) (a1 : bool) A A' B B', apstep a0 A A' -> apstep a1 B B' -> apstep (a0 || a1) (TPi A B) (TPi A' B')
| aps_TLam : forall (a0 : bool) b b', apstep a0 b b' -> apstep (a0) (TLam b) (TLam b')
| aps_TApp : forall (a0 : bool) (a1 : bool) f f' a a', apstep a0 f f' -> apstep a1 a a' -> apstep (a0 || a1) (TApp f a) (TApp f' a')
| aps_TSigma : forall (a0 : bool) (a1 : bool) A A' B B', apstep a0 A A' -> apstep a1 B B' -> apstep (a0 || a1) (TSigma A B) (TSigma A' B')
| aps_TPair : forall (a0 : bool) (a1 : bool) a a' b b', apstep a0 a a' -> apstep a1 b b' -> apstep (a0 || a1) (TPair a b) (TPair a' b')
| aps_TFst : forall (a0 : bool) p p', apstep a0 p p' -> apstep (a0) (TFst p) (TFst p')
| aps_TSnd : forall (a0 : bool) p p', apstep a0 p p' -> apstep (a0) (TSnd p) (TSnd p')
| aps_TUnitT : apstep false TUnitT TUnitT
| aps_TUnit : apstep false TUnit TUnit
| aps_TUId : apstep false TUId TUId
| aps_TTag : forall s, apstep false (TTag s) (TTag s)
| aps_TEnumU : apstep false TEnumU TEnumU
| aps_TNilE : apstep false TNilE TNilE
| aps_TConsE : forall (a0 : bool) (a1 : bool) tag tag' E E', apstep a0 tag tag' -> apstep a1 E E' -> apstep (a0 || a1) (TConsE tag E) (TConsE tag' E')
| aps_TEnumT : forall (a0 : bool) E E', apstep a0 E E' -> apstep (a0) (TEnumT E) (TEnumT E')
| aps_TEZero : apstep false TEZero TEZero
| aps_TESucc : forall (a0 : bool) n n', apstep a0 n n' -> apstep (a0) (TESucc n) (TESucc n')
| aps_TEPi : forall (a0 : bool) (a1 : bool) k E E' P P', apstep a0 E E' -> apstep a1 P P' -> apstep (a0 || a1) (TEPi k E P) (TEPi k E' P')
| aps_TSwitch : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) k E E' P P' p p' e e', apstep a0 E E' -> apstep a1 P P' -> apstep a2 p p' -> apstep a3 e e' -> apstep (a0 || a1 || a2 || a3) (TSwitch k E P p e) (TSwitch k E' P' p' e')
| aps_TIDesc : forall (a0 : bool) IT IT', apstep a0 IT IT' -> apstep (a0) (TIDesc IT) (TIDesc IT')
| aps_TIVar : forall (a0 : bool) i i', apstep a0 i i' -> apstep (a0) (TIVar i) (TIVar i')
| aps_TI1 : apstep false TI1 TI1
| aps_TIBot : apstep false TIBot TIBot
| aps_TIProd : forall (a0 : bool) (a1 : bool) A A' B B', apstep a0 A A' -> apstep a1 B B' -> apstep (a0 || a1) (TIProd A B) (TIProd A' B')
| aps_TIPi : forall (a0 : bool) (a1 : bool) A A' D D', apstep a0 A A' -> apstep a1 D D' -> apstep (a0 || a1) (TIPi A D) (TIPi A' D')
| aps_TISig : forall (a0 : bool) (a1 : bool) A A' D D', apstep a0 A A' -> apstep a1 D D' -> apstep (a0 || a1) (TISig A D) (TISig A' D')
| aps_TIChoice : forall (a0 : bool) (a1 : bool) E E' D D', apstep a0 E E' -> apstep a1 D D' -> apstep (a0 || a1) (TIChoice E D) (TIChoice E' D')
| aps_TInterp : forall (a0 : bool) (a1 : bool) (a2 : bool) IT IT' D D' X X', apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 X X' -> apstep (a0 || a1 || a2) (TInterp IT D X) (TInterp IT' D' X')
| aps_TMuI : forall (a0 : bool) (a1 : bool) IT IT' D D', apstep a0 IT IT' -> apstep a1 D D' -> apstep (a0 || a1) (TMuI IT D) (TMuI IT' D')
| aps_TIn : forall (a0 : bool) x x', apstep a0 x x' -> apstep (a0) (TIn x) (TIn x')
| aps_TInd : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) IT IT' D D' P P' s s' i i' x x', apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 P P' -> apstep a3 s s' -> apstep a4 i i' -> apstep a5 x x' -> apstep (a0 || a1 || a2 || a3 || a4 || a5) (TInd IT D P s i x) (TInd IT' D' P' s' i' x')
| aps_TIAll : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) IT IT' D D' X X' x x' P P', apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 X X' -> apstep a3 x x' -> apstep a4 P P' -> apstep (a0 || a1 || a2 || a3 || a4) (TIAll IT D X x P) (TIAll IT' D' X' x' P')
| aps_THyps : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) IT IT' D D' X X' P P' h h' x x', apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 X X' -> apstep a3 P P' -> apstep a4 h h' -> apstep a5 x x' -> apstep (a0 || a1 || a2 || a3 || a4 || a5) (THyps IT D X P h x) (THyps IT' D' X' P' h' x')
| aps_TClose : forall (a0 : bool) (a1 : bool) (a2 : bool) IT IT' F F' G G', apstep a0 IT IT' -> apstep a1 F F' -> apstep a2 G G' -> apstep (a0 || a1 || a2) (TClose IT F G) (TClose IT' F' G')
| aps_TCloseCase : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) (a6 : bool) k IT IT' F F' G G' i i' Q Q' b b' x x', apstep a0 IT IT' -> apstep a1 F F' -> apstep a2 G G' -> apstep a3 i i' -> apstep a4 Q Q' -> apstep a5 b b' -> apstep a6 x x' -> apstep (a0 || a1 || a2 || a3 || a4 || a5 || a6) (TCloseCase k IT F G i Q b x) (TCloseCase k IT' F' G' i' Q' b' x')
| aps_TCloseInd : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) (a6 : bool) IT IT' G G' P P' s s' F F' i i' x x', apstep a0 IT IT' -> apstep a1 G G' -> apstep a2 P P' -> apstep a3 s s' -> apstep a4 F F' -> apstep a5 i i' -> apstep a6 x x' -> apstep (a0 || a1 || a2 || a3 || a4 || a5 || a6) (TCloseInd IT G P s F i x) (TCloseInd IT' G' P' s' F' i' x')

| aps_beta : forall (a0 : bool) (a1 : bool) b b' a a', apstep a0 b b' -> apstep a1 a a' ->
    apstep true (TApp (TLam b) a) (subst a' 0 b')
| aps_fst_pair : forall (a0 : bool) a a' b, apstep a0 a a' -> apstep true (TFst (TPair a b)) a'
| aps_snd_pair : forall (a0 : bool) a b b', apstep a0 b b' -> apstep true (TSnd (TPair a b)) b'
| aps_epi_nil : forall k P, apstep true (TEPi k TNilE P) TUnitT
| aps_epi_cons : forall (a0 : bool) (a1 : bool) k tag E E' P P', apstep a0 E E' -> apstep a1 P P' ->
    apstep true (TEPi k (TConsE tag E) P)
      (TSigma (TApp P' TEZero)
        (TEPi k (lift 1 0 E')
          (TLam (TApp (lift 2 0 P') (TESucc (TVar 0))))))
| aps_switch_zero : forall (a0 : bool) k tag E P p p' ps, apstep a0 p p' ->
    apstep true (TSwitch k (TConsE tag E) P (TPair p ps) TEZero) p'
| aps_switch_succ : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) k tag E E' P P' p ps ps' n n',
    apstep a0 E E' -> apstep a1 P P' -> apstep a2 ps ps' -> apstep a3 n n' ->
    apstep true (TSwitch k (TConsE tag E) P (TPair p ps) (TESucc n))
      (TSwitch k E' (TLam (TApp (lift 1 0 P') (TESucc (TVar 0)))) ps' n')
| aps_interp_var : forall (a0 : bool) (a1 : bool) IT i i' X X', apstep a0 i i' -> apstep a1 X X' ->
    apstep true (TInterp IT (TIVar i) X) (TApp X' i')
| aps_interp_one : forall IT X, apstep true (TInterp IT TI1 X) TUnitT
| aps_interp_bot : forall IT X, apstep true (TInterp IT TIBot X) (TEnumT TNilE)
| aps_interp_prod : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) IT IT' A A' B B' X X',
    apstep a0 IT IT' -> apstep a1 A A' -> apstep a2 B B' -> apstep a3 X X' ->
    apstep true (TInterp IT (TIProd A B) X)
      (TSigma (TInterp IT' A' X')
        (TInterp (lift 1 0 IT') (lift 1 0 B') (lift 1 0 X')))
| aps_interp_pi : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) IT IT' A A' D D' X X',
    apstep a0 IT IT' -> apstep a1 A A' -> apstep a2 D D' -> apstep a3 X X' ->
    apstep true (TInterp IT (TIPi A D) X)
      (TPi A' (TInterp (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
        (lift 1 0 X')))
| aps_interp_sig : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) IT IT' A A' D D' X X',
    apstep a0 IT IT' -> apstep a1 A A' -> apstep a2 D D' -> apstep a3 X X' ->
    apstep true (TInterp IT (TISig A D) X)
      (TSigma A' (TInterp (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
        (lift 1 0 X')))
| aps_interp_choice : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) IT IT' E E' D D' X X',
    apstep a0 IT IT' -> apstep a1 E E' -> apstep a2 D D' -> apstep a3 X X' ->
    apstep true (TInterp IT (TIChoice E D) X)
      (TSigma (TEnumT E')
        (TInterp (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
          (lift 1 0 X')))
| aps_iall_var : forall (a0 : bool) (a1 : bool) (a2 : bool) IT i i' X x x' P P',
    apstep a0 i i' -> apstep a1 x x' -> apstep a2 P P' ->
    apstep true (TIAll IT (TIVar i) X x P) (TApp P' (TPair i' x'))
| aps_iall_one : forall IT X P, apstep true (TIAll IT TI1 X TUnit P) TUnitT
| aps_iall_bot : forall IT X x P, apstep true (TIAll IT TIBot X x P) TUnitT
| aps_iall_prod : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) (a6 : bool) IT IT' A A' B B' X X' a a' b b' P P',
    apstep a0 IT IT' -> apstep a1 A A' -> apstep a2 B B' -> apstep a3 X X' ->
    apstep a4 a a' -> apstep a5 b b' -> apstep a6 P P' ->
    apstep true (TIAll IT (TIProd A B) X (TPair a b) P)
      (TSigma (TIAll IT' A' X' a' P')
        (TIAll (lift 1 0 IT') (lift 1 0 B') (lift 1 0 X') (lift 1 0 b')
          (lift 1 0 P')))
| aps_iall_pi : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) IT IT' A A' D D' X X' f f' P P',
    apstep a0 IT IT' -> apstep a1 A A' -> apstep a2 D D' -> apstep a3 X X' ->
    apstep a4 f f' -> apstep a5 P P' ->
    apstep true (TIAll IT (TIPi A D) X f P)
      (TPi A' (TIAll (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
        (lift 1 0 X') (TApp (lift 1 0 f') (TVar 0)) (lift 1 0 P')))
| aps_iall_sig : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) IT IT' A D D' X X' a a' x x' P P',
    apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 X X' ->
    apstep a3 a a' -> apstep a4 x x' -> apstep a5 P P' ->
    apstep true (TIAll IT (TISig A D) X (TPair a x) P)
      (TIAll IT' (TApp D' a') X' x' P')
| aps_iall_choice : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) IT IT' E D D' X X' e e' x x' P P',
    apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 X X' ->
    apstep a3 e e' -> apstep a4 x x' -> apstep a5 P P' ->
    apstep true (TIAll IT (TIChoice E D) X (TPair e x) P)
      (TIAll IT' (TApp D' e') X' x' P')
| aps_hyps_var : forall (a0 : bool) (a1 : bool) (a2 : bool) IT i i' X P h h' x x',
    apstep a0 i i' -> apstep a1 h h' -> apstep a2 x x' ->
    apstep true (THyps IT (TIVar i) X P h x) (TApp (TApp h' i') x')
| aps_hyps_one : forall IT X P h, apstep true (THyps IT TI1 X P h TUnit) TUnit
| aps_hyps_bot : forall IT X P h x, apstep true (THyps IT TIBot X P h x) TUnit
| aps_hyps_prod : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) (a6 : bool) (a7 : bool) IT IT' A A' B B' X X' P P' h h' a a' b b',
    apstep a0 IT IT' -> apstep a1 A A' -> apstep a2 B B' -> apstep a3 X X' -> apstep a4 P P' ->
    apstep a5 h h' -> apstep a6 a a' -> apstep a7 b b' ->
    apstep true (THyps IT (TIProd A B) X P h (TPair a b))
      (TPair (THyps IT' A' X' P' h' a') (THyps IT' B' X' P' h' b'))
| aps_hyps_pi : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) IT IT' A D D' X X' P P' h h' f f',
    apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 X X' -> apstep a3 P P' ->
    apstep a4 h h' -> apstep a5 f f' ->
    apstep true (THyps IT (TIPi A D) X P h f)
      (TLam (THyps (lift 1 0 IT') (TApp (lift 1 0 D') (TVar 0))
        (lift 1 0 X') (lift 1 0 P') (lift 1 0 h')
        (TApp (lift 1 0 f') (TVar 0))))
| aps_hyps_sig : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) (a6 : bool) IT IT' A D D' X X' P P' h h' a a' x x',
    apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 X X' -> apstep a3 P P' ->
    apstep a4 h h' -> apstep a5 a a' -> apstep a6 x x' ->
    apstep true (THyps IT (TISig A D) X P h (TPair a x))
      (THyps IT' (TApp D' a') X' P' h' x')
| aps_hyps_choice : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) (a6 : bool) IT IT' E D D' X X' P P' h h' e e' x x',
    apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 X X' -> apstep a3 P P' ->
    apstep a4 h h' -> apstep a5 e e' -> apstep a6 x x' ->
    apstep true (THyps IT (TIChoice E D) X P h (TPair e x))
      (THyps IT' (TApp D' e') X' P' h' x')
| aps_ind_red : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) IT IT' D D' P P' st st' i i' xs xs',
    apstep a0 IT IT' -> apstep a1 D D' -> apstep a2 P P' -> apstep a3 st st' ->
    apstep a4 i i' -> apstep a5 xs xs' ->
    apstep true (TInd IT D P st i (TIn xs))
      (TApp (TApp (TApp st' i') xs')
        (THyps IT' (TApp D' i') (TMuI IT' D') P'
          (TLam (TLam (TInd (lift 2 0 IT') (lift 2 0 D') (lift 2 0 P')
            (lift 2 0 st') (TVar 1) (TVar 0)))) xs'))
| aps_closecase_red : forall (a0 : bool) (a1 : bool) k IT F G i Q b b' xs xs',
    apstep a0 b b' -> apstep a1 xs xs' ->
    apstep true (TCloseCase k IT F G i Q b (TIn xs)) (TApp b' xs')
| aps_closeind_red : forall (a0 : bool) (a1 : bool) (a2 : bool) (a3 : bool) (a4 : bool) (a5 : bool) (a6 : bool) IT IT' G G' P P' st st' F F' i i' xs xs',
    apstep a0 IT IT' -> apstep a1 G G' -> apstep a2 P P' -> apstep a3 st st' ->
    apstep a4 F F' -> apstep a5 i i' -> apstep a6 xs xs' ->
    apstep true (TCloseInd IT G P st F i (TIn xs))
      (TApp (TApp (TApp (TApp st' F') i') xs')
        (THyps IT' (TApp F' i') (TClose IT' G' G')
          (TLam (TApp (TApp (TApp (lift 1 0 P') (lift 1 0 G'))
            (TFst (TVar 0))) (TSnd (TVar 0))))
          (TLam (TLam (TCloseInd (lift 2 0 IT') (lift 2 0 G')
            (lift 2 0 P') (lift 2 0 st') (lift 2 0 G')
            (TVar 1) (TVar 0)))) xs')).

Ltac apply_active_root tac := first
    [ eapply aps_beta; tac
    | eapply aps_fst_pair; tac
    | eapply aps_snd_pair; tac
    | eapply aps_epi_nil; tac
    | eapply aps_epi_cons; tac
    | eapply aps_switch_zero; tac
    | eapply aps_switch_succ; tac
    | eapply aps_interp_var; tac
    | eapply aps_interp_one; tac
    | eapply aps_interp_bot; tac
    | eapply aps_interp_prod; tac
    | eapply aps_interp_pi; tac
    | eapply aps_interp_sig; tac
    | eapply aps_interp_choice; tac
    | eapply aps_iall_var; tac
    | eapply aps_iall_one; tac
    | eapply aps_iall_bot; tac
    | eapply aps_iall_prod; tac
    | eapply aps_iall_pi; tac
    | eapply aps_iall_sig; tac
    | eapply aps_iall_choice; tac
    | eapply aps_hyps_var; tac
    | eapply aps_hyps_one; tac
    | eapply aps_hyps_bot; tac
    | eapply aps_hyps_prod; tac
    | eapply aps_hyps_pi; tac
    | eapply aps_hyps_sig; tac
    | eapply aps_hyps_choice; tac
    | eapply aps_ind_red; tac
    | eapply aps_closecase_red; tac
    | eapply aps_closeind_red; tac ].

Lemma apstep_refl : forall t, apstep false t t.
Proof. induction t.
  - apply aps_TVar; assumption.
  - apply aps_TSort; assumption.
  - apply aps_TPi with (a0:=false) (a1:=false); assumption.
  - apply aps_TLam with (a0:=false); assumption.
  - apply aps_TApp with (a0:=false) (a1:=false); assumption.
  - apply aps_TSigma with (a0:=false) (a1:=false); assumption.
  - apply aps_TPair with (a0:=false) (a1:=false); assumption.
  - apply aps_TFst with (a0:=false); assumption.
  - apply aps_TSnd with (a0:=false); assumption.
  - apply aps_TUnitT; assumption.
  - apply aps_TUnit; assumption.
  - apply aps_TUId; assumption.
  - apply aps_TTag; assumption.
  - apply aps_TEnumU; assumption.
  - apply aps_TNilE; assumption.
  - apply aps_TConsE with (a0:=false) (a1:=false); assumption.
  - apply aps_TEnumT with (a0:=false); assumption.
  - apply aps_TEZero; assumption.
  - apply aps_TESucc with (a0:=false); assumption.
  - apply aps_TEPi with (a0:=false) (a1:=false); assumption.
  - apply aps_TSwitch with (a0:=false) (a1:=false) (a2:=false) (a3:=false); assumption.
  - apply aps_TIDesc with (a0:=false); assumption.
  - apply aps_TIVar with (a0:=false); assumption.
  - apply aps_TI1; assumption.
  - apply aps_TIBot; assumption.
  - apply aps_TIProd with (a0:=false) (a1:=false); assumption.
  - apply aps_TIPi with (a0:=false) (a1:=false); assumption.
  - apply aps_TISig with (a0:=false) (a1:=false); assumption.
  - apply aps_TIChoice with (a0:=false) (a1:=false); assumption.
  - apply aps_TInterp with (a0:=false) (a1:=false) (a2:=false); assumption.
  - apply aps_TMuI with (a0:=false) (a1:=false); assumption.
  - apply aps_TIn with (a0:=false); assumption.
  - apply aps_TInd with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false); assumption.
  - apply aps_TIAll with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false); assumption.
  - apply aps_THyps with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false); assumption.
  - apply aps_TClose with (a0:=false) (a1:=false) (a2:=false); assumption.
  - apply aps_TCloseCase with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false) (a6:=false); assumption.
  - apply aps_TCloseInd with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false) (a6:=false); assumption.
Qed.

Lemma apstep_pstep : forall a t u, apstep a t u -> pstep t u.
Proof. intros a t u H; induction H; solve [constructor; assumption]. Qed.

Lemma apstep_inactive : forall a t u, apstep a t u -> a = false -> t = u.
Proof. intros a t u H; induction H; intro HE; try discriminate;
  repeat rewrite Bool.orb_false_iff in HE; f_equal; tauto. Qed.

Lemma apstep_lift : forall a t u, apstep a t u -> forall d c,
  apstep a (lift d c t) (lift d c u).
Proof. intros a t u H; induction H; intros d c; cbn;
  try solve [apply apstep_refl | constructor; auto];
  lift_norm; apply_active_root ltac:(eauto). Qed.

Lemma root_apstep : forall t u, root_step t = Some u -> apstep true t u.
Proof. intros t u H; destruct t; cbn in H; try discriminate;
  repeat match goal with H : match ?x with _ => _ end = Some _ |- _ =>
    destruct x; try discriminate end;
  inversion H; subst; unfold product, Bot, carrier, diagonal_motive; cbn;
  repeat rewrite lift_one_one_zero; apply_active_root ltac:(apply apstep_refl). Qed.

Definition positive_computations t u :=
  exists v, computation t v /\ rtc computation v u.

Lemma positive_computations_tail : forall t u v,
  positive_computations t u -> rtc computation u v -> positive_computations t v.
Proof.
  intros t u v [w [Htw Hwu]] Huv. exists w; split;
    [exact Htw|eapply rtc_trans; eassumption].
Qed.
Lemma positive_computations_head : forall t u v,
  rtc computation t u -> positive_computations u v -> positive_computations t v.
Proof.
  intros t u v H; induction H; intro HP; [exact HP|].
  exists y; split; [exact H|]. destruct (IHrtc HP) as [w [Hw Hr]].
  eapply rtc_step; eassumption.
Qed.
Lemma positive_computations_map : forall C,
  (forall t u, computation t u -> computation (C t) (C u)) ->
  forall t u, positive_computations t u -> positive_computations (C t) (C u).
Proof.
  intros C HC t u [v [Htv Hvu]]. exists (C v); split; [now apply HC|].
  exact (rtc_map_rel _ _ computation computation C HC _ _ Hvu).
Qed.
Lemma apstep_computations : forall a t u,
  apstep a t u -> rtc computation t u.
Proof. intros; apply pstep_computations; eapply apstep_pstep; eassumption. Qed.

Ltac add_apstep_computations :=
  repeat match goal with H : apstep _ ?t ?u |- _ =>
    tryif match goal with HC : rtc computation t u |- _ => idtac end then fail else
    let HC := fresh "HC" in pose proof (apstep_computations _ _ _ H) as HC
  end.
Ltac positive_comp_congr :=
  match goal with
  | HP : positive_computations ?a ?b |- positive_computations ?s ?t =>
    match s with context C [a] =>
      let middle := context C [b] in
      let F := constr:(fun z : term => ltac:(let v := context C [z] in exact v)) in
      eapply positive_computations_tail with (u:=middle);
      [eapply (positive_computations_map F);
        [intros; solve [eauto 4 using computation]|exact HP]
      |comp_star_congr]
    end
  end.

Lemma apstep_positive : forall a t u, apstep a t u ->
  a = true -> positive_computations t u.
Proof.
  intros a t u H; induction H; intro HA; try discriminate.
  all: add_apstep_computations.
  all: try solve [repeat rewrite Bool.orb_true_iff in HA;
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
    match goal with IH : ?a = true -> positive_computations ?t ?u,
      HE : ?a = true |- _ =>
      pose proof (IH HE); positive_comp_congr end].
  all: match goal with |- positive_computations ?s ?t =>
    let develop := ltac:(fun rec t =>
      match goal with H : apstep _ t ?v |- _ => constr:(v) | _ =>
        lazymatch t with ?f ?a =>
          let df := rec rec f in let da := rec rec a in constr:(df da)
        | _ => constr:(t) end end) in
    let middle := develop develop s in
    eapply positive_computations_head with (u:=middle);
    [comp_star_congr|eexists; split;
      [apply cmp_root; cbn; unfold product, Bot, carrier, diagonal_motive;
        cbn; repeat rewrite lift_one_one_zero; reflexivity
      |apply rtc_refl]]
  end.
Qed.

Ltac active_congruence :=
  match goal with
  | |- apstep true (TPi _ _) _ =>
    first [ apply aps_TPi with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TPi with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TLam _) _ =>
    first [ apply aps_TLam with (a0:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TApp _ _) _ =>
    first [ apply aps_TApp with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TApp with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TSigma _ _) _ =>
    first [ apply aps_TSigma with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TSigma with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TPair _ _) _ =>
    first [ apply aps_TPair with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TPair with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TFst _) _ =>
    first [ apply aps_TFst with (a0:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TSnd _) _ =>
    first [ apply aps_TSnd with (a0:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TConsE _ _) _ =>
    first [ apply aps_TConsE with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TConsE with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TEnumT _) _ =>
    first [ apply aps_TEnumT with (a0:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TESucc _) _ =>
    first [ apply aps_TESucc with (a0:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TEPi _ _ _) _ =>
    first [ apply aps_TEPi with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TEPi with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TSwitch _ _ _ _ _) _ =>
    first [ apply aps_TSwitch with (a0:=true) (a1:=false) (a2:=false) (a3:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TSwitch with (a0:=false) (a1:=true) (a2:=false) (a3:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TSwitch with (a0:=false) (a1:=false) (a2:=true) (a3:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TSwitch with (a0:=false) (a1:=false) (a2:=false) (a3:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TIDesc _) _ =>
    first [ apply aps_TIDesc with (a0:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TIVar _) _ =>
    first [ apply aps_TIVar with (a0:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TIProd _ _) _ =>
    first [ apply aps_TIProd with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TIProd with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TIPi _ _) _ =>
    first [ apply aps_TIPi with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TIPi with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TISig _ _) _ =>
    first [ apply aps_TISig with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TISig with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TIChoice _ _) _ =>
    first [ apply aps_TIChoice with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TIChoice with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TInterp _ _ _) _ =>
    first [ apply aps_TInterp with (a0:=true) (a1:=false) (a2:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TInterp with (a0:=false) (a1:=true) (a2:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TInterp with (a0:=false) (a1:=false) (a2:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TMuI _ _) _ =>
    first [ apply aps_TMuI with (a0:=true) (a1:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TMuI with (a0:=false) (a1:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TIn _) _ =>
    first [ apply aps_TIn with (a0:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TInd _ _ _ _ _ _) _ =>
    first [ apply aps_TInd with (a0:=true) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TInd with (a0:=false) (a1:=true) (a2:=false) (a3:=false) (a4:=false) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TInd with (a0:=false) (a1:=false) (a2:=true) (a3:=false) (a4:=false) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TInd with (a0:=false) (a1:=false) (a2:=false) (a3:=true) (a4:=false) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TInd with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=true) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TInd with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TIAll _ _ _ _ _) _ =>
    first [ apply aps_TIAll with (a0:=true) (a1:=false) (a2:=false) (a3:=false) (a4:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TIAll with (a0:=false) (a1:=true) (a2:=false) (a3:=false) (a4:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TIAll with (a0:=false) (a1:=false) (a2:=true) (a3:=false) (a4:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TIAll with (a0:=false) (a1:=false) (a2:=false) (a3:=true) (a4:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TIAll with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (THyps _ _ _ _ _ _) _ =>
    first [ apply aps_THyps with (a0:=true) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_THyps with (a0:=false) (a1:=true) (a2:=false) (a3:=false) (a4:=false) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_THyps with (a0:=false) (a1:=false) (a2:=true) (a3:=false) (a4:=false) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_THyps with (a0:=false) (a1:=false) (a2:=false) (a3:=true) (a4:=false) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_THyps with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=true) (a5:=false); solve [eassumption|apply apstep_refl]
      | apply aps_THyps with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TClose _ _ _) _ =>
    first [ apply aps_TClose with (a0:=true) (a1:=false) (a2:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TClose with (a0:=false) (a1:=true) (a2:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TClose with (a0:=false) (a1:=false) (a2:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TCloseCase _ _ _ _ _ _ _ _) _ =>
    first [ apply aps_TCloseCase with (a0:=true) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseCase with (a0:=false) (a1:=true) (a2:=false) (a3:=false) (a4:=false) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseCase with (a0:=false) (a1:=false) (a2:=true) (a3:=false) (a4:=false) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseCase with (a0:=false) (a1:=false) (a2:=false) (a3:=true) (a4:=false) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseCase with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=true) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseCase with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=true) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseCase with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false) (a6:=true); solve [eassumption|apply apstep_refl] ]
  | |- apstep true (TCloseInd _ _ _ _ _ _ _) _ =>
    first [ apply aps_TCloseInd with (a0:=true) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseInd with (a0:=false) (a1:=true) (a2:=false) (a3:=false) (a4:=false) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseInd with (a0:=false) (a1:=false) (a2:=true) (a3:=false) (a4:=false) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseInd with (a0:=false) (a1:=false) (a2:=false) (a3:=true) (a4:=false) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseInd with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=true) (a5:=false) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseInd with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=true) (a6:=false); solve [eassumption|apply apstep_refl]
      | apply aps_TCloseInd with (a0:=false) (a1:=false) (a2:=false) (a3:=false) (a4:=false) (a5:=false) (a6:=true); solve [eassumption|apply apstep_refl] ]
  end.

Lemma computation_apstep : forall t u, computation t u -> apstep true t u.
Proof. intros t u H; induction H; try solve [now apply root_apstep].
  all: active_congruence. Qed.
