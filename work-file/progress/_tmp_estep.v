Require Import Progress _tmp_epstep _tmp_eta_shape _tmp_epstep_inv
  _tmp_eta_tool _tmp_epstep_subst _tmp_epstep_diamond.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* ====================================================================== *)
(*  estep — a single eta step (root or under congruence).                 *)
(* ====================================================================== *)

Inductive estep : term -> term -> Prop :=
| es_eta : forall f, estep (TLam (TApp (lift 1 0 f) (TVar 0))) f
| es_pi1 : forall A A' B, estep A A' -> estep (TPi A B) (TPi A' B)
| es_pi2 : forall A B B', estep B B' -> estep (TPi A B) (TPi A B')
| es_lam : forall b b', estep b b' -> estep (TLam b) (TLam b')
| es_app1 : forall f f' a, estep f f' -> estep (TApp f a) (TApp f' a)
| es_app2 : forall f a a', estep a a' -> estep (TApp f a) (TApp f a')
| es_sigma1 : forall A A' B, estep A A' -> estep (TSigma A B) (TSigma A' B)
| es_sigma2 : forall A B B', estep B B' -> estep (TSigma A B) (TSigma A B')
| es_pair1 : forall a a' b, estep a a' -> estep (TPair a b) (TPair a' b)
| es_pair2 : forall a b b', estep b b' -> estep (TPair a b) (TPair a b')
| es_fst : forall p p', estep p p' -> estep (TFst p) (TFst p')
| es_snd : forall p p', estep p p' -> estep (TSnd p) (TSnd p')
| es_conse1 : forall t t' E, estep t t' -> estep (TConsE t E) (TConsE t' E)
| es_conse2 : forall t E E', estep E E' -> estep (TConsE t E) (TConsE t E')
| es_enumt : forall E E', estep E E' -> estep (TEnumT E) (TEnumT E')
| es_esucc : forall n n', estep n n' -> estep (TESucc n) (TESucc n')
| es_epi1 : forall E E' P, estep E E' -> estep (TEPi E P) (TEPi E' P)
| es_epi2 : forall E P P', estep P P' -> estep (TEPi E P) (TEPi E P')
| es_switch1 : forall E E' P p e, estep E E' ->
    estep (TSwitch E P p e) (TSwitch E' P p e)
| es_switch2 : forall E P P' p e, estep P P' ->
    estep (TSwitch E P p e) (TSwitch E P' p e)
| es_switch3 : forall E P p p' e, estep p p' ->
    estep (TSwitch E P p e) (TSwitch E P p' e)
| es_switch4 : forall E P p e e', estep e e' ->
    estep (TSwitch E P p e) (TSwitch E P p e')
| es_idesc : forall IT IT', estep IT IT' -> estep (TIDesc IT) (TIDesc IT')
| es_ivar : forall i i', estep i i' -> estep (TIVar i) (TIVar i')
| es_iprod1 : forall A A' B, estep A A' -> estep (TIProd A B) (TIProd A' B)
| es_iprod2 : forall A B B', estep B B' -> estep (TIProd A B) (TIProd A B')
| es_ipi1 : forall S S' T, estep S S' -> estep (TIPi S T) (TIPi S' T)
| es_ipi2 : forall S T T', estep T T' -> estep (TIPi S T) (TIPi S T')
| es_isig1 : forall S S' T, estep S S' -> estep (TISig S T) (TISig S' T)
| es_isig2 : forall S T T', estep T T' -> estep (TISig S T) (TISig S T')
| es_ichoice1 : forall E E' T, estep E E' ->
    estep (TIChoice E T) (TIChoice E' T)
| es_ichoice2 : forall E T T', estep T T' ->
    estep (TIChoice E T) (TIChoice E T')
| es_interp1 : forall D D' X, estep D D' -> estep (TInterp D X) (TInterp D' X)
| es_interp2 : forall D X X', estep X X' -> estep (TInterp D X) (TInterp D X')
| es_mui : forall R R', estep R R' -> estep (TMuI R) (TMuI R')
| es_mus : forall S S', estep S S' -> estep (TMuS S) (TMuS S')
| es_in : forall x x', estep x x' -> estep (TIn x) (TIn x')
| es_ind1 : forall R R' P s i x, estep R R' ->
    estep (TInd R P s i x) (TInd R' P s i x)
| es_ind2 : forall R P P' s i x, estep P P' ->
    estep (TInd R P s i x) (TInd R P' s i x)
| es_ind3 : forall R P s s' i x, estep s s' ->
    estep (TInd R P s i x) (TInd R P s' i x)
| es_ind4 : forall R P s i i' x, estep i i' ->
    estep (TInd R P s i x) (TInd R P s i' x)
| es_ind5 : forall R P s i x x', estep x x' ->
    estep (TInd R P s i x) (TInd R P s i x')
| es_iall1 : forall D D' X xs P, estep D D' ->
    estep (TIAll D X xs P) (TIAll D' X xs P)
| es_iall2 : forall D X X' xs P, estep X X' ->
    estep (TIAll D X xs P) (TIAll D X' xs P)
| es_iall3 : forall D X xs xs' P, estep xs xs' ->
    estep (TIAll D X xs P) (TIAll D X xs' P)
| es_iall4 : forall D X xs P P', estep P P' ->
    estep (TIAll D X xs P) (TIAll D X xs P')
| es_hyps1 : forall D D' X P h xs, estep D D' ->
    estep (THyps D X P h xs) (THyps D' X P h xs)
| es_hyps2 : forall D X X' P h xs, estep X X' ->
    estep (THyps D X P h xs) (THyps D X' P h xs)
| es_hyps3 : forall D X P P' h xs, estep P P' ->
    estep (THyps D X P h xs) (THyps D X P' h xs)
| es_hyps4 : forall D X P h h' xs, estep h h' ->
    estep (THyps D X P h xs) (THyps D X P h' xs)
| es_hyps5 : forall D X P h xs xs', estep xs xs' ->
    estep (THyps D X P h xs) (THyps D X P h xs')
| es_list : forall A A', estep A A' -> estep (TList A) (TList A')
| es_lnil : forall A A', estep A A' -> estep (TLNil A) (TLNil A')
| es_lcons1 : forall A A' a l, estep A A' ->
    estep (TLCons A a l) (TLCons A' a l)
| es_lcons2 : forall A a a' l, estep a a' ->
    estep (TLCons A a l) (TLCons A a' l)
| es_lcons3 : forall A a l l', estep l l' ->
    estep (TLCons A a l) (TLCons A a l')
| es_case1 : forall M M' Q bs, estep M M' ->
    estep (TCase M Q bs) (TCase M' Q bs)
| es_case2 : forall M Q Q' bs, estep Q Q' ->
    estep (TCase M Q bs) (TCase M Q' bs)
| es_case_br1 : forall M Q bs1 c c' b bs2, estep c c' ->
    estep (TCase M Q (bs1 ++ (c, b) :: bs2))
          (TCase M Q (bs1 ++ (c', b) :: bs2))
| es_case_br2 : forall M Q bs1 c b b' bs2, estep b b' ->
    estep (TCase M Q (bs1 ++ (c, b) :: bs2))
          (TCase M Q (bs1 ++ (c, b') :: bs2)).

(* Parallel beta/computation reduction.  Eta is kept separate below; this
   relation contracts any collection of old redexes at once. *)
