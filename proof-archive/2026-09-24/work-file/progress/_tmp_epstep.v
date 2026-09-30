Require Import Progress.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

(* Parallel contextual eta reduction, with no beta/computation roots. *)
Inductive epstep : term -> term -> Prop :=
| eps_var : forall n, epstep (TVar n) (TVar n)
| eps_sort : forall k, epstep (TSort k) (TSort k)
| eps_pi : forall A A' B B', epstep A A' -> epstep B B' ->
    epstep (TPi A B) (TPi A' B')
| eps_lam : forall b b', epstep b b' -> epstep (TLam b) (TLam b')
| eps_app : forall f f' a a', epstep f f' -> epstep a a' ->
    epstep (TApp f a) (TApp f' a')
| eps_sigma : forall A A' B B', epstep A A' -> epstep B B' ->
    epstep (TSigma A B) (TSigma A' B')
| eps_pair : forall a a' b b', epstep a a' -> epstep b b' ->
    epstep (TPair a b) (TPair a' b')
| eps_fst : forall p p', epstep p p' -> epstep (TFst p) (TFst p')
| eps_snd : forall p p', epstep p p' -> epstep (TSnd p) (TSnd p')
| eps_unitt : epstep TUnitT TUnitT
| eps_unit : epstep TUnit TUnit
| eps_uid : epstep TUId TUId
| eps_tag : forall s, epstep (TTag s) (TTag s)
| eps_enumu : epstep TEnumU TEnumU
| eps_nile : epstep TNilE TNilE
| eps_conse : forall t t' E E', epstep t t' -> epstep E E' ->
    epstep (TConsE t E) (TConsE t' E')
| eps_enumt : forall E E', epstep E E' -> epstep (TEnumT E) (TEnumT E')
| eps_ezero : epstep TEZero TEZero
| eps_esucc : forall n n', epstep n n' -> epstep (TESucc n) (TESucc n')
| eps_epi : forall E E' P P', epstep E E' -> epstep P P' ->
    epstep (TEPi E P) (TEPi E' P')
| eps_switch : forall E E' P P' p p' e e',
    epstep E E' -> epstep P P' -> epstep p p' -> epstep e e' ->
    epstep (TSwitch E P p e) (TSwitch E' P' p' e')
| eps_idesc : forall I I', epstep I I' -> epstep (TIDesc I) (TIDesc I')
| eps_ivar : forall i i', epstep i i' -> epstep (TIVar i) (TIVar i')
| eps_i1 : epstep TI1 TI1
| eps_iprod : forall A A' B B', epstep A A' -> epstep B B' ->
    epstep (TIProd A B) (TIProd A' B')
| eps_ipi : forall S S' T T', epstep S S' -> epstep T T' ->
    epstep (TIPi S T) (TIPi S' T')
| eps_isig : forall S S' T T', epstep S S' -> epstep T T' ->
    epstep (TISig S T) (TISig S' T')
| eps_ichoice : forall E E' T T', epstep E E' -> epstep T T' ->
    epstep (TIChoice E T) (TIChoice E' T')
| eps_interp : forall D D' X X', epstep D D' -> epstep X X' ->
    epstep (TInterp D X) (TInterp D' X')
| eps_mui : forall R R', epstep R R' -> epstep (TMuI R) (TMuI R')
| eps_mus : forall S S', epstep S S' -> epstep (TMuS S) (TMuS S')
| eps_in : forall x x', epstep x x' -> epstep (TIn x) (TIn x')
| eps_ind : forall R R' P P' s s' i i' x x',
    epstep R R' -> epstep P P' -> epstep s s' -> epstep i i' -> epstep x x' ->
    epstep (TInd R P s i x) (TInd R' P' s' i' x')
| eps_iall : forall D D' X X' xs xs' P P',
    epstep D D' -> epstep X X' -> epstep xs xs' -> epstep P P' ->
    epstep (TIAll D X xs P) (TIAll D' X' xs' P')
| eps_hyps : forall D D' X X' P P' h h' xs xs',
    epstep D D' -> epstep X X' -> epstep P P' -> epstep h h' -> epstep xs xs' ->
    epstep (THyps D X P h xs) (THyps D' X' P' h' xs')
| eps_list : forall A A', epstep A A' -> epstep (TList A) (TList A')
| eps_lnil : forall A A', epstep A A' -> epstep (TLNil A) (TLNil A')
| eps_lcons : forall A A' a a' l l',
    epstep A A' -> epstep a a' -> epstep l l' ->
    epstep (TLCons A a l) (TLCons A' a' l')
| eps_case : forall M M' Q Q' bs bs',
    epstep M M' -> epstep Q Q' -> epbranches bs bs' ->
    epstep (TCase M Q bs) (TCase M' Q' bs')
| eps_eta : forall f f', epstep f f' ->
    epstep (TLam (TApp (lift 1 0 f) (TVar 0))) f'
with epbranches : list (term * term) -> list (term * term) -> Prop :=
| epbs_nil : epbranches [] []
| epbs_cons : forall c c' b b' bs bs',
    epstep c c' -> epstep b b' -> epbranches bs bs' ->
    epbranches ((c,b)::bs) ((c',b')::bs').

Scheme epstep_ind' := Induction for epstep Sort Prop
with epbranches_ind' := Induction for epbranches Sort Prop.
Combined Scheme epstep_epbranches_ind from epstep_ind', epbranches_ind'.

Lemma epstep_refl : forall t, epstep t t.
Proof.
  apply (tsize_strong_ind (fun t => epstep t t)).
  intros t IH. destruct t;
    try pose proof (tsize_pos t) as Ht;
    try pose proof (tsize_pos t1) as Ht1;
    try pose proof (tsize_pos t2) as Ht2;
    try pose proof (tsize_pos t3) as Ht3;
    try pose proof (tsize_pos t4) as Ht4;
    try pose proof (tsize_pos t5) as Ht5;
    try solve [constructor];
    try (constructor; repeat (apply IH; cbn; lia)).
  induction bs as [|[c b] bs IHbs]; [constructor |].
  constructor.
  - apply IH. eapply tsize_case_bs. left. reflexivity.
  - apply IH. eapply tsize_case_bs_body. left. reflexivity.
  - apply IHbs. intros u Hu. apply IH. cbn in *. lia.
Qed.

Lemma epbranches_refl : forall bs, epbranches bs bs.
Proof.
  induction bs as [|[c b] bs IH]; constructor;
    eauto using epstep_refl.
Qed.

Lemma epstep_lift_mut :
  (forall t u (H : epstep t u), forall d k,
      epstep (lift d k t) (lift d k u)) /\
  (forall bs bs' (H : epbranches bs bs'), forall d k,
      epbranches
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
        (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs')).
Proof.
  apply epstep_epbranches_ind; cbn; intros;
    try solve [constructor; eauto using epstep_refl].
  - apply epstep_refl.
  - repeat rewrite (lift_lift_one_zero _ d k).
    eapply eps_eta; eauto.
Qed.

Corollary epstep_lift : forall t u, epstep t u -> forall d k,
    epstep (lift d k t) (lift d k u).
Proof. intros t u H d k. exact (proj1 epstep_lift_mut t u H d k). Qed.

Corollary epbranches_lift : forall bs bs', epbranches bs bs' -> forall d k,
    epbranches
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs)
      (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs').
Proof. intros bs bs' H d k. exact (proj2 epstep_lift_mut bs bs' H d k). Qed.
