Require Import Progress _tmp_epstep _tmp_eta_shape _tmp_epstep_inv _tmp_eta_tool.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Ltac take_join :=
  match goal with
  | IH : forall z, epstep ?s z ->
        exists w, epstep ?t w /\ epstep z w,
    H : epstep ?s ?z |- _ =>
      first [ constr_eq z t; fail 1
            | let w := fresh "w" in
              let Hl := fresh "Hleft" in
              let Hr := fresh "Hright" in
              destruct (IH z H) as [w [Hl Hr]];
              clear IH ]
  | IH : forall zs, epbranches ?ss zs ->
        exists ws, epbranches ?ts ws /\ epbranches zs ws,
    H : epbranches ?ss ?zs |- _ =>
      first [ constr_eq zs ts; fail 1
            | let ws := fresh "ws" in
              let Hl := fresh "Hleft" in
              let Hr := fresh "Hright" in
              destruct (IH zs H) as [ws [Hl Hr]];
              clear IH ]
  end.

Ltac invert_other :=
  match goal with
  | Hother : epstep ?s ?u
      |- exists v, epstep ?t v /\ epstep ?u v =>
      inversion Hother; subst; clear Hother
  | Hother : epbranches ?ss ?us
      |- exists vs, epbranches ?ts vs /\ epbranches ?us vs =>
      inversion Hother; subst; clear Hother
  end.

Lemma epstep_diamond_mut :
  (forall s t (H : epstep s t), forall u, epstep s u ->
      exists v, epstep t v /\ epstep u v) /\
  (forall ss ts (H : epbranches ss ts), forall us, epbranches ss us ->
      exists vs, epbranches ts vs /\ epbranches us vs).
Proof.
  apply epstep_epbranches_ind.
  all: intros.
  all: invert_other.
  all: repeat take_join.
  all: try solve [eexists; split; econstructor; eassumption].
  - match goal with
    | IH : forall z, epstep (TApp (lift 1 0 ?f) (TVar 0)) z -> _,
      E : epstep (TApp (lift 1 0 f) (TVar 0)) ?b',
      Hfu : epstep f ?u |- _ =>
      destruct (eta_app_inv f b' E) as [g [Hbg Hfg]];
      subst b';
      assert (Hbodyu : epstep
        (TApp (lift 1 0 f) (TVar 0))
        (TApp (lift 1 0 u) (TVar 0))) by
        (constructor; [apply epstep_lift; exact Hfu | constructor]);
      destruct (IH _ Hbodyu) as [v [Hgv Huv]];
      destruct (eta_app_inv g v Hgv) as [x [Hvx Hgx]];
      destruct (eta_app_inv u v Huv) as [y [Hvy Huy]]
    end.
    assert (Hxy : x = y).
    { rewrite Hvx in Hvy. inversion Hvy.
      apply lift_one_injective with (k := 0). assumption. }
    subst y. exists x. split.
    + apply eps_eta. exact Hgx.
    + exact Huy.
  - match goal with
    | IH : forall z, epstep ?f z -> _,
      Hb : epstep (TApp (lift 1 0 f) (TVar 0)) ?b' |- _ =>
      destruct (eta_app_inv f b' Hb) as [g [Hbg Hfg]];
      subst b';
      destruct (IH g Hfg) as [w [Hfw Hgw]];
      exists w; split; [exact Hfw | apply eps_eta; exact Hgw]
    end.
  - apply lift_one_injective in H1. subst f0.
    exact (H u H2).
Qed.

Corollary epstep_diamond : forall s t u,
    epstep s t -> epstep s u ->
    exists v, epstep t v /\ epstep u v.
Proof.
  intros s t u Hst Hsu.
  exact (proj1 epstep_diamond_mut s t Hst u Hsu).
Qed.

Corollary epbranches_diamond : forall ss ts us,
    epbranches ss ts -> epbranches ss us ->
    exists vs, epbranches ts vs /\ epbranches us vs.
Proof.
  intros ss ts us Hst Hsu.
  exact (proj2 epstep_diamond_mut ss ts Hst us Hsu).
Qed.
