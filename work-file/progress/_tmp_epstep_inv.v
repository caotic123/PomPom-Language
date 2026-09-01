Require Import Progress _tmp_epstep _tmp_eta_shape.
From Stdlib Require Import List Lia PeanoNat.
Import ListNotations TypeRules.

Lemma tsize_lift_inv_local : forall t d k, tsize (lift d k t) = tsize t.
Proof.
  assert (Hmap : forall bs d k,
      (forall c b, In (c,b) bs ->
        tsize (lift d k c) = tsize c /\
        tsize (lift d (S k) b) = tsize b) ->
      bsize (map (fun '(c,b) => (lift d k c, lift d (S k) b)) bs) =
      bsize bs).
  {
    intros bs d k H.
    induction bs as [|[c b] bs IH]; cbn; [reflexivity |].
    rewrite (proj1 (H c b (or_introl eq_refl))).
    rewrite (proj2 (H c b (or_introl eq_refl))).
    rewrite (IH ltac:(intros c' b' Hin; apply H; right; exact Hin)).
    reflexivity.
  }
  apply (tsize_strong_ind (fun t => forall d k,
    tsize (lift d k t) = tsize t)).
  intros t IH d k. destruct t; cbn [lift tsize].
  all: try solve [destruct (Nat.ltb n k); reflexivity].
  all: try solve [
    repeat erewrite IH by
      (try (pose proof (tsize_pos t1));
       try (pose proof (tsize_pos t2));
       try (pose proof (tsize_pos t3));
       try (pose proof (tsize_pos t4));
       try (pose proof (tsize_pos t5)); cbn; lia);
    reflexivity].
  rewrite (IH t1 ltac:(pose proof (tsize_pos t2); cbn; lia) d k).
  rewrite (IH t2 ltac:(pose proof (tsize_pos t1); cbn; lia) d k).
  rewrite (Hmap bs d k ltac:(intros c b Hin; split;
    [apply IH; eapply tsize_case_bs; exact Hin |
     apply IH; eapply tsize_case_bs_body; exact Hin])).
  reflexivity.
Qed.

Lemma epbranches_lift_inv_bound : forall N,
    (forall f, tsize f < N -> forall k T,
      epstep (lift 1 k f) T ->
      exists u, T = lift 1 k u /\ epstep f u) ->
    forall bs k BS, bsize bs < N ->
      epbranches
        (map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) bs) BS ->
      exists us,
        BS = map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) us /\
        epbranches bs us.
Proof.
  intros N H bs. induction bs as [|[c b] bs IHbs];
    intros k BS Hsize Hep; cbn in Hep.
  - inversion Hep; subst. exists []; split; constructor.
  - inversion Hep; subst.
    match goal with
    | Hc : epstep (lift 1 k c) ?c' ,
      Hb : epstep (lift 1 (S k) b) ?b',
      Hbs : epbranches
        (map (fun '(c0,b0) =>
          (lift 1 k c0, lift 1 (S k) b0)) bs) ?bs' |- _ =>
      destruct (H c ltac:(pose proof (tsize_pos b); cbn in Hsize; lia)
        k c' Hc) as [u [Hu Hcu]];
      destruct (H b ltac:(pose proof (tsize_pos c); cbn in Hsize; lia)
        (S k) b' Hb) as [v [Hv Hbv]];
      destruct (IHbs k bs' ltac:(cbn in Hsize; lia) Hbs)
        as [us [Hus Hbus]]
    end.
    subst. exists ((u,v)::us). split; [reflexivity |].
    constructor; assumption.
Qed.

Ltac ep_inv_child IH :=
  match goal with
  | Hs : epstep (lift 1 ?q ?x) ?y |- _ =>
      let u := fresh "u" in
      let He := fresh "Heq" in
      let Hp := fresh "Hep" in
      destruct (IH x ltac:(cbn; lia) q y Hs) as [u [He Hp]];
      subst y
  end.

Lemma epstep_lift_inv : forall f k T,
    epstep (lift 1 k f) T ->
    exists u, T = lift 1 k u /\ epstep f u.
Proof.
  apply (tsize_strong_ind (fun f => forall k T,
    epstep (lift 1 k f) T ->
    exists u, T = lift 1 k u /\ epstep f u)).
  intros f IH k T Hstep.
  destruct f; cbn [lift] in Hstep.
  - destruct (Nat.ltb n k) eqn:Hlt; inversion Hstep; subst.
    + exists (TVar n). split;
        [cbn [lift]; rewrite Hlt; reflexivity | exact (eps_var n)].
    + exists (TVar n). split;
        [cbn [lift]; rewrite Hlt; reflexivity | exact (eps_var n)].
  - inversion Hstep; subst. exists (TSort k0); split; constructor.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TPi A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst.
    + ep_inv_child IH. exists (TLam u). split; [reflexivity | constructor; assumption].
    + assert (Hshapeeq :
          lift 1 k (TLam f) = TLam (TApp (lift 1 0 f0) (TVar 0))) by
        (cbn [lift]; f_equal; symmetry; assumption).
      pose proof (lift_eta_shape_decomp_k (TLam f) f0 k Hshapeeq) as Hshape.
      destruct Hshape as [u [Hfu Hsource]].
      subst f0.
      assert (Husize : tsize u < tsize (TLam f)).
      { pose proof (tsize_lift_inv_local u 1 0) as Hlift_size.
        rewrite Hsource. cbn [tsize]. lia. }
      destruct (IH u Husize k T H0)
        as [v [Hv Huv]].
      subst T. exists v. split; [reflexivity |].
      rewrite Hsource. constructor. assumption.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TApp A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TSigma A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TPair A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TFst u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TSnd u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. exists TUnitT; split; constructor.
  - inversion Hstep; subst. exists TUnit; split; constructor.
  - inversion Hstep; subst. exists TUId; split; constructor.
  - inversion Hstep; subst. exists (TTag s); split; constructor.
  - inversion Hstep; subst. exists TEnumU; split; constructor.
  - inversion Hstep; subst. exists TNilE; split; constructor.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TConsE A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TEnumT u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. exists TEZero; split; constructor.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TESucc u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TEPi A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?A, H2 : epstep f2 ?B,
      H3 : epstep f3 ?p, H4 : epstep f4 ?e |- _ =>
      exists (TSwitch A B p e); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TIDesc u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TIVar u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. exists TI1; split; constructor.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TIProd A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TIPi A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TISig A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TIChoice A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TInterp A B); split; [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TMuI u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TMuS u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TIn u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?a1, H2 : epstep f2 ?a2,
      H3 : epstep f3 ?a3, H4 : epstep f4 ?a4,
      H5 : epstep f5 ?a5 |- _ =>
      exists (TInd a1 a2 a3 a4 a5); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?a1, H2 : epstep f2 ?a2,
      H3 : epstep f3 ?a3, H4 : epstep f4 ?a4 |- _ =>
      exists (TIAll a1 a2 a3 a4); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?a1, H2 : epstep f2 ?a2,
      H3 : epstep f3 ?a3, H4 : epstep f4 ?a4,
      H5 : epstep f5 ?a5 |- _ =>
      exists (THyps a1 a2 a3 a4 a5); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TList u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. ep_inv_child IH.
    exists (TLNil u). split; [reflexivity | constructor; assumption].
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | H1 : epstep f1 ?a1, H2 : epstep f2 ?a2,
      H3 : epstep f3 ?a3 |- _ =>
      exists (TLCons a1 a2 a3); split;
        [reflexivity | constructor; assumption]
    end.
  - inversion Hstep; subst. repeat ep_inv_child IH.
    match goal with
    | Hbs : epbranches
        (map (fun '(c,b) => (lift 1 k c, lift 1 (S k) b)) bs) ?BS |- _ =>
      destruct (epbranches_lift_inv_bound (tsize (TCase f1 f2 bs))
        (fun x Hx q Y HY => IH x Hx q Y HY)
        bs k BS ltac:(cbn; lia) Hbs) as [us [Hus Heps]]
    end.
    subst.
    match goal with HA : epstep f1 ?A, HB : epstep f2 ?B |- _ =>
      exists (TCase A B us); split;
        [reflexivity | constructor; assumption]
    end.
Qed.
