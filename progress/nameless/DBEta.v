From Stdlib Require Import List Arith Lia PeanoNat String.
Require Export nameless.DBParallelBase.
Import ListNotations.

Inductive epstep : term -> term -> Prop :=
| eps_TVar : forall n, epstep (TVar n) (TVar n)
| eps_TSort : forall k, epstep (TSort k) (TSort k)
| eps_TPi : forall A A' B B', epstep A A' -> epstep B B' -> epstep (TPi A B) (TPi A' B')
| eps_TLam : forall b b', epstep b b' -> epstep (TLam b) (TLam b')
| eps_TApp : forall f f' a a', epstep f f' -> epstep a a' -> epstep (TApp f a) (TApp f' a')
| eps_TSigma : forall A A' B B', epstep A A' -> epstep B B' -> epstep (TSigma A B) (TSigma A' B')
| eps_TPair : forall a a' b b', epstep a a' -> epstep b b' -> epstep (TPair a b) (TPair a' b')
| eps_TFst : forall p p', epstep p p' -> epstep (TFst p) (TFst p')
| eps_TSnd : forall p p', epstep p p' -> epstep (TSnd p) (TSnd p')
| eps_TUnitT : epstep TUnitT TUnitT
| eps_TUnit : epstep TUnit TUnit
| eps_TUId : epstep TUId TUId
| eps_TTag : forall s, epstep (TTag s) (TTag s)
| eps_TEnumU : epstep TEnumU TEnumU
| eps_TNilE : epstep TNilE TNilE
| eps_TConsE : forall tag tag' E E', epstep tag tag' -> epstep E E' -> epstep (TConsE tag E) (TConsE tag' E')
| eps_TEnumT : forall E E', epstep E E' -> epstep (TEnumT E) (TEnumT E')
| eps_TEZero : epstep TEZero TEZero
| eps_TESucc : forall n n', epstep n n' -> epstep (TESucc n) (TESucc n')
| eps_TEPi : forall k E E' P P', epstep E E' -> epstep P P' -> epstep (TEPi k E P) (TEPi k E' P')
| eps_TSwitch : forall k E E' P P' p p' e e', epstep E E' -> epstep P P' -> epstep p p' -> epstep e e' -> epstep (TSwitch k E P p e) (TSwitch k E' P' p' e')
| eps_TIDesc : forall IT IT', epstep IT IT' -> epstep (TIDesc IT) (TIDesc IT')
| eps_TIVar : forall i i', epstep i i' -> epstep (TIVar i) (TIVar i')
| eps_TI1 : epstep TI1 TI1
| eps_TIBot : epstep TIBot TIBot
| eps_TIProd : forall A A' B B', epstep A A' -> epstep B B' -> epstep (TIProd A B) (TIProd A' B')
| eps_TIPi : forall A A' D D', epstep A A' -> epstep D D' -> epstep (TIPi A D) (TIPi A' D')
| eps_TISig : forall A A' D D', epstep A A' -> epstep D D' -> epstep (TISig A D) (TISig A' D')
| eps_TIChoice : forall E E' D D', epstep E E' -> epstep D D' -> epstep (TIChoice E D) (TIChoice E' D')
| eps_TInterp : forall IT IT' D D' X X', epstep IT IT' -> epstep D D' -> epstep X X' -> epstep (TInterp IT D X) (TInterp IT' D' X')
| eps_TMuI : forall IT IT' D D', epstep IT IT' -> epstep D D' -> epstep (TMuI IT D) (TMuI IT' D')
| eps_TIn : forall x x', epstep x x' -> epstep (TIn x) (TIn x')
| eps_TInd : forall IT IT' D D' P P' s s' i i' x x', epstep IT IT' -> epstep D D' -> epstep P P' -> epstep s s' -> epstep i i' -> epstep x x' -> epstep (TInd IT D P s i x) (TInd IT' D' P' s' i' x')
| eps_TIAll : forall IT IT' D D' X X' x x' P P', epstep IT IT' -> epstep D D' -> epstep X X' -> epstep x x' -> epstep P P' -> epstep (TIAll IT D X x P) (TIAll IT' D' X' x' P')
| eps_THyps : forall IT IT' D D' X X' P P' h h' x x', epstep IT IT' -> epstep D D' -> epstep X X' -> epstep P P' -> epstep h h' -> epstep x x' -> epstep (THyps IT D X P h x) (THyps IT' D' X' P' h' x')
| eps_TClose : forall IT IT' F F' G G', epstep IT IT' -> epstep F F' -> epstep G G' -> epstep (TClose IT F G) (TClose IT' F' G')
| eps_TCloseCase : forall k IT IT' F F' G G' i i' Q Q' b b' x x', epstep IT IT' -> epstep F F' -> epstep G G' -> epstep i i' -> epstep Q Q' -> epstep b b' -> epstep x x' -> epstep (TCloseCase k IT F G i Q b x) (TCloseCase k IT' F' G' i' Q' b' x')
| eps_TCloseInd : forall IT IT' G G' P P' s s' F F' i i' x x', epstep IT IT' -> epstep G G' -> epstep P P' -> epstep s s' -> epstep F F' -> epstep i i' -> epstep x x' -> epstep (TCloseInd IT G P s F i x) (TCloseInd IT' G' P' s' F' i' x')

| eps_eta : forall f f', epstep f f' ->
    epstep (TLam (TApp (lift 1 0 f) (TVar 0))) f'.

Lemma epstep_refl : forall t, epstep t t.
Proof. induction t; constructor; assumption. Qed.

Lemma epstep_lift : forall t u, epstep t u -> forall d c,
  epstep (lift d c t) (lift d c u).
Proof.
  intros t u H; induction H; intros d c; cbn;
    try solve [apply epstep_refl | constructor; auto].
  rewrite lift_lift_one_zero. apply eps_eta. apply IHepstep.
Qed.



Lemma epstep_subst : forall t t', epstep t t' -> forall u u' c,
  epstep u u' -> epstep (subst u c t) (subst u' c t').
Proof.
  intros t t' H. induction H; intros u u' c Hu; cbn [subst];
    try solve [constructor; auto].
  - destruct (n <? c); [apply epstep_refl|].
    destruct (n =? c); auto using epstep_lift, epstep_refl.
  - rewrite subst_lift_one_zero. apply eps_eta. now apply IHepstep.
Qed.

Lemma epstep_lift_inverse : forall t T,
  epstep t T -> forall f k, t = lift 1 k f ->
  exists u, T = lift 1 k u /\ epstep f u.
Proof.
  intros t T Hstep; induction Hstep; intros original cutoff Heq.
  all: try solve [
    match goal with
    | H : TLam (TApp (lift 1 0 ?f) (TVar 0)) = lift 1 ?cutoff ?original,
      IH : forall f0 k, ?f = lift 1 k f0 -> _ |- _ =>
      destruct (lift_eta_shape_decomp_k original f cutoff (eq_sym H)) as [v [Hv Hshape]];
      subst f; destruct (IH v cutoff eq_refl) as [w [Hw Hvw]];
      exists w; split; [exact Hw|rewrite Hshape; now apply eps_eta]
    end].
  all: destruct original; cbn [lift] in Heq; try discriminate;
    try match type of Heq with context [Nat.ltb ?n ?cut] => destruct (n <? cut) eqn:Hlt end;
    try discriminate; inversion Heq; subst.
  all: repeat match goal with
    | IH : forall f k, lift 1 ?q ?tm = lift 1 k f ->
        exists u, ?out = lift 1 k u /\ epstep f u |- _ =>
      let new := fresh "new" in let E := fresh "E" in let Hnew := fresh "Hnew" in
      destruct (IH tm q eq_refl) as [new [E Hnew]]; clear IH; subst out
    end.
  all: eexists; split; [|constructor; eassumption]; cbn [lift]; try rewrite Hlt; reflexivity.
Qed.

Lemma eta_app_inverse : forall f t,
  epstep (TApp (lift 1 0 f) (TVar 0)) t ->
  exists u, t = TApp (lift 1 0 u) (TVar 0) /\ epstep f u.
Proof.
  intros f t H. inversion H; subst.
  match goal with H : epstep (TVar 0) _ |- _ => inversion H; subst end.
  match goal with H : epstep (lift 1 0 f) ?f' |- _ =>
    destruct (epstep_lift_inverse _ _ H f 0 eq_refl) as [u [Hu Hfu]];
    exists u; split; [now rewrite Hu|exact Hfu]
  end.
Qed.

Ltac eta_take_join :=
  match goal with
  | IH : forall z, epstep ?s z -> exists w, epstep ?t w /\ epstep z w,
    H : epstep ?s ?z |- _ =>
    first [constr_eq z t; fail 1 |
      let w := fresh "w" in let Hl := fresh "Hl" in let Hr := fresh "Hr" in
      destruct (IH z H) as [w [Hl Hr]]; clear IH]
  end.

Lemma epstep_diamond : diamond epstep.
Proof.
  intros s t u H; revert u. induction H; intros u Hother;
    inversion Hother; subst; clear Hother.
  all: repeat eta_take_join.
  all: try solve [eexists; split; econstructor; eassumption].
  - match goal with
    | IH : forall z, epstep (TApp (lift 1 0 ?f) (TVar 0)) z -> _,
      E : epstep (TApp (lift 1 0 ?f) (TVar 0)) ?b',
      Hfu : epstep ?f ?u |- _ =>
      destruct (eta_app_inverse f b' E) as [g [Hbg Hfg]]; subst b';
      assert (Hbodyu : epstep (TApp (lift 1 0 f) (TVar 0))
        (TApp (lift 1 0 u) (TVar 0))) by
        (constructor; [now apply epstep_lift | constructor]);
      destruct (IH _ Hbodyu) as [v [Hgv Huv]];
      destruct (eta_app_inverse g v Hgv) as [x [Hvx Hgx]];
      destruct (eta_app_inverse u v Huv) as [y [Hvy Huy]]
    end.
    assert (Hxy : x = y).
    { rewrite Hvx in Hvy. inversion Hvy. eapply lift_one_injective; eassumption. }
    subst y. exists x. split; [now apply eps_eta|assumption].
  - match goal with
    | IH : forall z, epstep ?f z -> _,
      Hb : epstep (TApp (lift 1 0 ?f) (TVar 0)) ?b' |- _ =>
      destruct (eta_app_inverse f b' Hb) as [g [Hbg Hfg]]; subst b';
      destruct (IH g Hfg) as [w [Hfw Hgw]];
      exists w; split; [exact Hfw|now apply eps_eta]
    end.
  - match goal with H : lift 1 0 ?f = lift 1 0 ?g |- _ =>
      apply lift_one_injective in H; subst g end.
    eauto.
Qed.
