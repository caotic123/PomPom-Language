(* Progress infrastructure for the named calculus. The binding, reduction,
   and shape lemmas have no metatheory assumptions. Canonical forms and
   progress are proved with conversion joinability as an explicit premise;
   no theorem or conjecture from OpenSignaturesTheorems is imported here. *)
From Stdlib Require Import List Arith Bool Lia.
Require Export OpenSignaturesBinding.
Import ListNotations.

Inductive head_tag :=
| h_sort | h_pi | h_sigma | h_unitT | h_unit | h_uid | h_tag
| h_enumu | h_nile | h_conse | h_enumt | h_zero | h_succ
| h_idesc | h_ivar | h_i1 | h_ibot | h_iprod | h_ipi | h_isig | h_ichoice
| h_mui | h_muapp | h_close | h_closeapp | h_in.

Definition term_head t :=
  match t with
  | TSort _ => Some h_sort | TPi _ _ _ => Some h_pi
  | TSigma _ _ _ => Some h_sigma | TUnitT => Some h_unitT
  | TUnit => Some h_unit | TUId => Some h_uid | TTag _ => Some h_tag
  | TEnumU => Some h_enumu | TNilE => Some h_nile | TConsE _ _ => Some h_conse
  | TEnumT _ => Some h_enumt | TEZero => Some h_zero | TESucc _ => Some h_succ
  | TIDesc _ => Some h_idesc | TIVar _ => Some h_ivar
  | TI1 => Some h_i1 | TIBot => Some h_ibot | TIProd _ _ => Some h_iprod
  | TIPi _ _ => Some h_ipi | TISig _ _ => Some h_isig | TIChoice _ _ => Some h_ichoice
  | TMuI _ _ => Some h_mui | TApp (TMuI _ _) _ => Some h_muapp
  | TClose _ _ _ => Some h_close | TApp (TClose _ _ _) _ => Some h_closeapp
  | TIn _ => Some h_in | _ => None
  end.

Lemma root_has_no_rigid_head : forall t u,
  root_step t = Some u -> term_head t = None.
Proof.
  destruct t; intros u H; cbn [root_step term_head] in *;
    try discriminate; try reflexivity.
  destruct t1; cbn in *; try discriminate; reflexivity.
Qed.

Lemma reduction_head : forall t u, reduction t u ->
  forall h, term_head t = Some h -> term_head u = Some h.
Proof.
  intros t u H; induction H; intros hdtag Hhead;
    try solve [exact Hhead | discriminate Hhead].
  - pose proof (root_has_no_rigid_head _ _ H). congruence.
  - destruct f; cbn [term_head] in Hhead; try discriminate;
      specialize (IHreduction _ eq_refl); destruct f';
      cbn [term_head] in *; try congruence;
      destruct f'1; discriminate.
Qed.

Lemma reduces_head : forall t u, reduces t u ->
  forall h, term_head t = Some h -> term_head u = Some h.
Proof. intros t u H; induction H; eauto using reduction_head. Qed.

Lemma alpha_head : forall t u, alpha_equiv t u ->
  forall h, term_head t = Some h -> term_head u = Some h.
Proof.
  destruct t; destruct u; intros Ha h Hh;
    cbn [term_head alpha_equiv alpha_eqb alpha_eqb_in] in *;
    try discriminate; try congruence.
  destruct t1; destruct u1; cbn [term_head alpha_eqb_in] in *;
    try discriminate; try congruence.
Qed.

Lemma reduction_conv : forall t u, reduction t u -> conv t u.
Proof.
  intros t u H; induction H; eauto using cv_step, st_root, cv_eta;
    apply cv_compatible; constructor; auto using cv_refl.
Qed.

Lemma reduces_conv : forall t u, reduces t u -> conv t u.
Proof. intros t u H; induction H; eauto using cv_refl, cv_trans, reduction_conv. Qed.

Section Conversion.
Hypothesis joinability : forall Gamma t u A,
  typing Gamma t A -> typing Gamma u A -> conv t u ->
  exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.

Lemma formed_join : forall Gamma t u,
  type_wf Gamma t -> type_wf Gamma u -> conv t u ->
  exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.
Proof.
  intros Gamma t u [j Hj] [k Hk] Hconv.
  eapply joinability with (A := TSort (Nat.max j k));
    eauto using ty_cumul, Nat.le_max_l, Nat.le_max_r.
Qed.

Lemma formed_head : forall Gamma t u h k,
  type_wf Gamma t -> type_wf Gamma u -> conv t u ->
  term_head t = Some h -> term_head u = Some k -> h = k.
Proof.
  intros Gamma t u h k Ht Hu Hc Hh Hk.
  destruct (formed_join _ _ _ Ht Hu Hc) as [w [w' [Hw [Hw' Ha]]]].
  pose proof (reduces_head _ _ Hw _ Hh) as Hwh.
  pose proof (reduces_head _ _ Hw' _ Hk) as Hwk.
  pose proof (alpha_head _ _ Ha _ Hwh). congruence.
Qed.

End Conversion.

Lemma reduces_trans : forall t u v, reduces t u -> reduces u v -> reduces t v.
Proof. intros t u v H; induction H; eauto using reduces. Qed.

Lemma reduction_sort : forall k u, reduction (TSort k) u -> u = TSort k.
Proof. intros k u H; inversion H; subst; cbn [root_step] in *; discriminate. Qed.

Lemma reduces_sort : forall k u, reduces (TSort k) u -> u = TSort k.
Proof.
  intros k u H; remember (TSort k) as t eqn:Ht; induction H; subst; auto.
  apply reduction_sort in H; subst; auto.
Qed.

Lemma reduction_pi : forall x A B u, reduction (TPi x A B) u ->
  exists A' B', u = TPi x A' B' /\ reduces A A' /\ reduces B B'.
Proof.
  intros x A B u H; inversion H; subst; cbn [root_step] in *;
    try discriminate; eauto 6 using reduces.
Qed.

Lemma reduces_pi : forall x A B u, reduces (TPi x A B) u ->
  exists A' B', u = TPi x A' B' /\ reduces A A' /\ reduces B B'.
Proof.
  intros x A B u H; remember (TPi x A B) as t eqn:Ht.
  revert x A B Ht; induction H; intros x0 A B Ht; subst.
  - eauto using reduces.
  - destruct (reduction_pi _ _ _ _ H) as [A' [B' [-> [HA HB]]]].
    destruct (IHreduces x0 A' B' eq_refl) as [C [D [-> [HC HD]]]].
    exists C, D. repeat split; eauto using reduces_trans.
Qed.

Lemma alpha_sort_right : forall t xs ys k,
  alpha_eqb_in xs ys t (TSort k) = true -> t = TSort k.
Proof.
  destruct t; intros xs ys level Ha; cbn in Ha; try discriminate.
  apply Nat.eqb_eq in Ha; congruence.
Qed.

Lemma conv_subst : forall t u s x,
  conv t u -> conv (subst s x t) (subst s x u).
Proof.
  intros t u s x H.
  eapply cv_trans with (u := TApp (TLam x t) s).
  - apply cv_sym, cv_step, st_root. reflexivity.
  - eapply cv_trans with (u := TApp (TLam x u) s).
    + apply cv_compatible, cp_TApp; [|apply cv_refl].
      now apply cv_compatible, cp_TLam.
    + apply cv_step, st_root. reflexivity.
Qed.

Inductive canonical_type : term -> term -> Prop :=
| ct_sort : forall k j, canonical_type (TSort k) (TSort j)
| ct_pi : forall x A B j, canonical_type (TPi x A B) (TSort j)
| ct_sigma : forall x A B j, canonical_type (TSigma x A B) (TSort j)
| ct_lam : forall x b y A B, canonical_type (TLam x b) (TPi y A B)
| ct_pair : forall a b x A B, canonical_type (TPair a b) (TSigma x A B)
| ct_unitT : forall j, canonical_type TUnitT (TSort j)
| ct_unit : canonical_type TUnit TUnitT
| ct_uid : forall j, canonical_type TUId (TSort j)
| ct_tag : forall s, canonical_type (TTag s) TUId
| ct_enumu : forall j, canonical_type TEnumU (TSort j)
| ct_nile : canonical_type TNilE TEnumU
| ct_conse : forall s E, canonical_type (TConsE s E) TEnumU
| ct_enumt : forall E j, canonical_type (TEnumT E) (TSort j)
| ct_zero : forall tag E, canonical_type TEZero (TEnumT (TConsE tag E))
| ct_succ : forall n tag E, canonical_type (TESucc n) (TEnumT (TConsE tag E))
| ct_idesc : forall IT j, canonical_type (TIDesc IT) (TSort j)
| ct_ivar : forall i IT, canonical_type (TIVar i) (TIDesc IT)
| ct_i1 : forall IT, canonical_type TI1 (TIDesc IT)
| ct_ibot : forall IT, canonical_type TIBot (TIDesc IT)
| ct_iprod : forall A B IT, canonical_type (TIProd A B) (TIDesc IT)
| ct_ipi : forall A D IT, canonical_type (TIPi A D) (TIDesc IT)
| ct_isig : forall A D IT, canonical_type (TISig A D) (TIDesc IT)
| ct_ichoice : forall E D IT, canonical_type (TIChoice E D) (TIDesc IT)
| ct_mui : forall IT D x A, canonical_type (TMuI IT D) (TPi x A (TSort 0))
| ct_muapp : forall IT D i j, canonical_type (TApp (TMuI IT D) i) (TSort j)
| ct_close : forall IT F G x A, canonical_type (TClose IT F G) (TPi x A (TSort 0))
| ct_closeapp : forall IT F G i j, canonical_type (TApp (TClose IT F G) i) (TSort j)
| ct_in_mu : forall xs IT D i, canonical_type (TIn xs) (MuAt IT D i)
| ct_in_close : forall xs IT F G i, canonical_type (TIn xs) (CloseAt IT F G i).

Lemma canonical_type_head : forall t A, canonical_type t A ->
  exists h, term_head A = Some h.
Proof. intros t A H; destruct H; eexists; reflexivity. Qed.

Lemma canonical_type_alpha : forall t A u,
  canonical_type t A -> alpha_equiv t u -> canonical_type u A.
Proof.
  intros t A u H; destruct H; destruct u; intros Ha;
    cbn [alpha_equiv alpha_eqb alpha_eqb_in] in Ha;
    try discriminate; try solve [constructor].
  all: destruct u1; cbn [alpha_eqb_in] in Ha; try discriminate; constructor.
Qed.

Lemma canonical_type_sort : forall t A k,
  canonical_type t A -> term_head A = Some h_sort -> canonical_type t (TSort k).
Proof. intros t A k H; destruct H; cbn; intro Hhd; try discriminate; constructor. Qed.

Lemma value_app_shape : forall f a, value (TApp f a) ->
  (exists IT D, f = TMuI IT D) \/ (exists IT F G, f = TClose IT F G).
Proof. intros f a H; inversion H; subst; eauto 6. Qed.

Lemma value_alpha : forall t u, value t -> alpha_equiv t u -> value u.
Proof.
  intros t u H; destruct H; destruct u; intros Ha;
    cbn [alpha_equiv alpha_eqb alpha_eqb_in MuAt CloseAt] in Ha;
    try discriminate; try solve [constructor].
  all: destruct u1; cbn [alpha_eqb_in] in Ha; try discriminate; constructor.
Qed.

Lemma typing_context : forall Gamma t A, typing Gamma t A -> wf Gamma.
Proof. intros Gamma t A H; induction H; assumption. Qed.

Lemma family_formation : forall Gamma IT,
  typing Gamma IT (TSort 0) -> typing Gamma (Family IT) (TSort 1).
Proof.
  intros Gamma IT HIT. destruct (exists_fresh_id Gamma []) as [z [Hz _]].
  eapply ty_alpha with (t := TPi z IT (TSort 0)).
  - eapply ty_pi with (j := 0) (k := 1); [exact Hz|exact HIT|].
    apply ty_sort. eapply wf_cons; eauto using typing_context.
  - unfold Family, alpha_equiv, alpha_eqb; cbn [alpha_eqb_in].
    rewrite alpha_eqb_in_refl. reflexivity.
Qed.

Lemma mu_at_formation : forall Gamma IT D i,
  typing Gamma IT (TSort 0) -> typing Gamma D (Def IT) -> typing Gamma i IT ->
  typing Gamma (MuAt IT D i) (TSort 0).
Proof.
  intros Gamma IT D i HIT HD Hi. unfold MuAt.
  change (typing Gamma (TApp (TMuI IT D) i) (subst i (fresh [IT]) (TSort 0))).
  eapply ty_app; [apply family_formation|apply ty_mui|]; eassumption.
Qed.

Lemma close_at_formation : forall Gamma IT F G i,
  typing Gamma IT (TSort 0) -> typing Gamma F (Def IT) ->
  typing Gamma G (Def IT) -> typing Gamma i IT ->
  typing Gamma (CloseAt IT F G i) (TSort 0).
Proof.
  intros Gamma IT F G i HIT HF HG Hi. unfold CloseAt.
  change (typing Gamma (TApp (TClose IT F G) i) (subst i (fresh [IT]) (TSort 0))).
  eapply ty_app; [apply family_formation|apply ty_close|]; eassumption.
Qed.

Local Ltac canonical_formation :=
  unfold type_wf;
  lazymatch goal with
  | |- exists _, typing _ TUnitT _ => exists 0
  | _ => eexists
  end;
  solve [eauto 4 using ty_sort, ty_unitT, ty_uid,
    ty_enumu, ty_enumt, ty_conse, ty_nile, ty_idesc,
    ty_epi, ty_interp, wf_nil, family_formation, mu_at_formation, close_at_formation].

Section Canonical.
Hypothesis joinability : forall Gamma t u A,
  typing Gamma t A -> typing Gamma u A -> conv t u ->
  exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.

Lemma pi_sort_codomain : forall Gamma y C x A B,
  type_wf Gamma (TPi y C (TSort 0)) -> type_wf Gamma (TPi x A B) ->
  conv (TPi y C (TSort 0)) (TPi x A B) -> conv B (TSort 0).
Proof.
  intros Gamma y C x A B Hy Hx Hc.
  destruct (formed_join joinability _ _ _ Hy Hx Hc)
    as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_pi _ _ _ _ Hw) as [C' [U [-> [HC HU]]]].
  destruct (reduces_pi _ _ _ _ Hw') as [A' [B' [-> [HA HB]]]].
  apply reduces_sort in HU. subst U.
  apply alpha_eqb_in_sym in Ha.
  cbn [alpha_eqb_in] in Ha. apply andb_true_iff in Ha.
  destruct Ha as [_ Ha]. apply alpha_sort_right in Ha. subst B'.
  now apply reduces_conv.
Qed.

Lemma canonical_representation : forall Gamma t A,
  typing Gamma t A -> value t ->
  exists B, typing Gamma t B /\ type_wf Gamma B /\ conv B A /\ canonical_type t B.
Proof.
  intros Gamma t A Hty; induction Hty; intros Hv;
    try solve [inversion Hv];
    assert (Hctx : wf Gamma) by (eauto 2 using typing_context);
    try solve [eexists; split; [solve [eauto 2 using typing]|
      split; [canonical_formation|split; [apply cv_refl|constructor]]]].
  - destruct (value_app_shape _ _ Hv) as [[IT [D ->]]|[IT [F [G ->]]]]; (
      destruct (IHHty2 ltac:(constructor)) as [T [HT [HF [Hc HC]]]];
      inversion HC; subst;
      assert (HB : conv B (TSort 0)) by
        (eapply pi_sort_codomain; [exact HF|exists k; exact Hty1|exact Hc]);
      assert (Hs : conv (subst a x B) (TSort 0)) by
        (change (conv (subst a x B) (subst a x (TSort 0))); now apply conv_subst);
      exists (TSort 0); split;
        [eapply ty_conv; [eapply ty_app; eassumption|
          apply ty_sort; exact Hctx|exact Hs]|
         split; [canonical_formation|
           split; [apply cv_sym; exact Hs|first [apply ct_muapp|apply ct_closeapp]]]]).
  - assert (Hvt : value t) by (eapply value_alpha; [exact Hv|now apply alpha_eqb_in_sym]).
    destruct (IHHty Hvt) as [T [HT [HF [Hc HC]]]].
    exists T; repeat split; eauto using ty_alpha, canonical_type_alpha.
  - destruct (IHHty1 Hv) as [T [HT [HF [Hc HC]]]].
    exists T; repeat split; eauto using cv_trans.
  - destruct (IHHty Hv) as [T [HT [HF [Hc HC]]]].
    destruct (canonical_type_head _ _ HC) as [hd Hhd].
    assert (E : hd = h_sort).
    { eapply (formed_head joinability Gamma T (TSort j)); [exact HF|
        canonical_formation|exact Hc|exact Hhd|reflexivity]. }
    subst hd. exists (TSort k); split; [eauto using ty_cumul|].
    split; [canonical_formation|split; [apply cv_refl|eauto using canonical_type_sort]].
Qed.
End Canonical.

Local Ltac alpha_shapes :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | H : (match ?un with _ => _ end) = true |- _ =>
      is_var un; destruct un; cbn [alpha_eqb_in] in H; try discriminate;
        repeat rewrite andb_true_iff in H
  | H : alpha_eqb_in ?xs ?ys ?tm ?un = true |- _ =>
      is_var un;
      tryif is_var tm then fail else
      (destruct un; cbn [alpha_eqb_in] in H; try discriminate;
        repeat rewrite andb_true_iff in H)
  end.

Lemma root_exists_alpha : forall t t' u,
  root_step t = Some t' -> alpha_equiv t u -> exists u', root_step u = Some u'.
Proof.
  destruct t; intros t' u Hr Ha; cbn [root_step] in Hr; try discriminate.
  all: repeat match type of Hr with
    | (match ?tm with _ => _ end) = Some _ =>
      destruct tm; cbn [root_step] in Hr; try discriminate
    end.
  all: unfold alpha_equiv, alpha_eqb in Ha; alpha_shapes.
  all: eexists; reflexivity.
Qed.

Lemma step_exists_alpha : forall t t', step t t' -> forall u,
  alpha_equiv t u -> exists u', step u u'.
Proof.
  intros t t' H; induction H; intros un Ha.
  { destruct (root_exists_alpha _ _ _ H Ha) as [u' Hu]. eauto using st_root. }
  all: unfold alpha_equiv, alpha_eqb in Ha; alpha_shapes.
  all: match goal with
    | IH : forall un, alpha_equiv ?tm un -> _,
      Ha : alpha_eqb_in [] [] ?tm ?un = true |- _ =>
        destruct (IH un Ha) as [v Hv]
    end.
  all: eauto using step.
Qed.

Lemma reduction_enumt : forall E u, reduction (TEnumT E) u ->
  exists E', u = TEnumT E' /\ reduces E E'.
Proof.
  intros E u H; inversion H; subst; cbn [root_step] in *;
    try discriminate; eauto using reduces.
Qed.

Lemma reduces_enumt : forall E u, reduces (TEnumT E) u ->
  exists E', u = TEnumT E' /\ reduces E E'.
Proof.
  intros E u H; remember (TEnumT E) as t eqn:Ht.
  revert E Ht; induction H; intros E Ht; subst.
  - eauto using reduces.
  - destruct (reduction_enumt _ _ H) as [E' [-> HE]].
    destruct (IHreduces _ eq_refl) as [E'' [-> HE']].
    exists E''. split; [reflexivity|eauto using reduces_trans].
Qed.

Section Shapes.
Hypothesis joinability : forall Gamma t u A,
  typing Gamma t A -> typing Gamma u A -> conv t u ->
  exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.

Lemma enum_cons_nil_absurd : forall Gamma tag E,
  type_wf Gamma (TEnumT (TConsE tag E)) -> type_wf Gamma Bot ->
  conv (TEnumT (TConsE tag E)) Bot -> False.
Proof.
  intros Gamma tag E Hcons Hnil Hc.
  destruct (formed_join joinability _ _ _ Hcons Hnil Hc)
    as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_enumt _ _ Hw) as [E1 [-> HE1]].
  destruct (reduces_enumt _ _ Hw') as [E2 [-> HE2]].
  pose proof (reduces_head _ _ HE1 _ eq_refl) as H1.
  pose proof (reduces_head _ _ HE2 _ eq_refl) as H2.
  change (alpha_equiv E1 E2) in Ha.
  pose proof (alpha_head _ _ Ha _ H1). congruence.
Qed.

Lemma bottom_no_value : forall Gamma t, typing Gamma t Bot -> value t -> False.
Proof.
  intros Gamma t Hty Hv. pose proof (typing_context _ _ _ Hty) as Hctx.
  destruct (canonical_representation joinability _ _ _ Hty Hv)
    as [B [HB [HF [Hc HC]]]].
  destruct (canonical_type_head _ _ HC) as [h Hh].
  assert (E : h = h_enumt).
  { eapply (formed_head joinability Gamma B Bot); [exact HF|canonical_formation|exact Hc|exact Hh|reflexivity]. }
  subst h. inversion HC; subst; cbn [term_head MuAt CloseAt] in Hh;
    try discriminate; (eapply enum_cons_nil_absurd;
    [exact HF|canonical_formation|exact Hc]).
Qed.
End Shapes.

(* Types whose next outer computation has a fixed constructor. This invariant
   avoids assuming subject reduction while establishing progress. *)
Inductive exposes_head : term -> head_tag -> Prop :=
| exposes_rigid : forall t h, term_head t = Some h -> exposes_head t h
| exposes_epi_nil : forall k P, exposes_head (TEPi k TNilE P) h_unitT
| exposes_epi_cons : forall k tag E P, exposes_head (TEPi k (TConsE tag E) P) h_sigma
| exposes_interp_unit : forall IT X, exposes_head (TInterp IT TI1 X) h_unitT
| exposes_interp_bot : forall IT X, exposes_head (TInterp IT TIBot X) h_enumt
| exposes_interp_prod : forall IT A B X, exposes_head (TInterp IT (TIProd A B) X) h_sigma
| exposes_interp_pi : forall IT A D X, exposes_head (TInterp IT (TIPi A D) X) h_pi
| exposes_interp_sig : forall IT A D X, exposes_head (TInterp IT (TISig A D) X) h_sigma
| exposes_interp_choice : forall IT E D X, exposes_head (TInterp IT (TIChoice E D) X) h_sigma.

Lemma exposes_head_reduction : forall t h u,
  exposes_head t h -> reduction t u -> exposes_head u h.
Proof.
  intros t h u He Hr. destruct He.
  { apply exposes_rigid. eapply reduction_head; eassumption. }
  all: inversion Hr; subst; try solve [constructor].
  all: try solve [match goal with H : root_step _ = Some _ |- _ =>
      cbn [root_step] in H; inversion H; subst; apply exposes_rigid; reflexivity end].
  all: match goal with H : reduction ?tm ?un |- _ =>
    let hd := eval hnf in (term_head tm) in
    lazymatch hd with Some ?tag =>
      let Hh := fresh "Hh" in pose proof (reduction_head tm un H tag eq_refl) as Hh;
      destruct un; cbn [term_head] in Hh; try discriminate;
      try solve [constructor];
      match type of Hh with (match ?f with _ => _ end) = _ => destruct f; discriminate end
    end
  end.
Qed.

Lemma exposes_head_reduces : forall t h u,
  exposes_head t h -> reduces t u -> exposes_head u h.
Proof.
  intros t h u He Hr; revert He; induction Hr; eauto using exposes_head_reduction.
Qed.

Lemma exposes_head_rigid : forall t h k,
  exposes_head t h -> term_head t = Some k -> h = k.
Proof. intros t h k H; destruct H; cbn [term_head]; congruence. Qed.

Section ExposedValues.
Hypothesis joinability : forall Gamma t u A,
  typing Gamma t A -> typing Gamma u A -> conv t u ->
  exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.

Lemma value_type_exposes : forall Gamma t A h,
  typing Gamma t A -> type_wf Gamma A -> value t -> exposes_head A h ->
  exists B, canonical_type t B /\ term_head B = Some h.
Proof.
  intros Gamma t A h Hty HA Hv He.
  destruct (canonical_representation joinability _ _ _ Hty Hv)
    as [B [HB [HF [Hc HC]]]].
  destruct (canonical_type_head _ _ HC) as [h' Hh'].
  destruct (formed_join joinability _ _ _ HF HA Hc) as [w [w' [Hw [Hw' Ha]]]].
  pose proof (reduces_head _ _ Hw _ Hh') as Hwh.
  pose proof (alpha_head _ _ Ha _ Hwh) as Hwh'.
  pose proof (exposes_head_reduces _ _ _ He Hw') as Hew'.
  assert (E : h = h') by (eapply exposes_head_rigid; eassumption).
  subst h'. eauto.
Qed.
End ExposedValues.

Section Progress.
Hypothesis joinability : forall Gamma t u A,
  typing Gamma t A -> typing Gamma u A -> conv t u ->
  exists w w', reduces t w /\ reduces u w' /\ alpha_equiv w w'.

Local Ltac canonical_at HT HV hd R :=
  let C := fresh "C" in let HC := fresh "HC" in let Hhead := fresh "Hhead" in
  match type of HT with
  | typing ?Gamma ?tm ?ty =>
      let HF := constr:(ltac:(canonical_formation) : type_wf Gamma ty) in
      destruct (value_type_exposes joinability
        Gamma tm ty hd HT HF HV R) as [C [HC Hhead]];
      inversion HC; subst; cbn [term_head MuAt CloseAt] in Hhead; try discriminate
  end.

Local Ltac canonical HT HV hd :=
  match type of HT with typing _ _ ?ty =>
    canonical_at HT HV hd (@exposes_rigid ty hd eq_refl)
  end.

Local Ltac canonical_unfold HT HV :=
  match type of HT with typing _ _ ?ty =>
    let out := eval hnf in (root_step ty) in
    lazymatch out with Some ?ty' =>
      let hd := eval hnf in (term_head ty') in
      lazymatch hd with Some ?tag =>
        let He := constr:(ltac:(eauto 2 using exposes_head) : exposes_head ty tag) in
        canonical_at HT HV tag He
      end
    end
  end.

Local Ltac progress_argument IH HV :=
  destruct (IH eq_refl) as [HV|[u Hu]];
    [|right; eexists; solve [eauto using step]].

Local Ltac root_progress := right; eexists; apply st_root; reflexivity.

Theorem progress_from_conversion : forall Gamma t A,
  typing Gamma t A -> Gamma = empty_ctx -> value t \/ exists u, step t u.
Proof.
  intros Gamma t A Hty; induction Hty; intros Hempty; subst Gamma;
    try solve [left; constructor].
  - discriminate H0.
  - progress_argument IHHty2 Hv. canonical Hty2 Hv h_pi;
      solve [root_progress | left; constructor].
  - progress_argument IHHty2 Hv. canonical Hty2 Hv h_sigma. root_progress.
  - progress_argument IHHty2 Hv. canonical Hty2 Hv h_sigma. root_progress.
  - destruct (IHHty eq_refl) as [Hv|[v Hr]].
    + left. eauto using value_alpha.
    + right. eauto using step_exists_alpha.
  - exact (IHHty1 eq_refl).
  - exact (IHHty eq_refl).
  - progress_argument IHHty1 Hv. canonical Hty1 Hv h_enumu; root_progress.
  - progress_argument IHHty1 HE.
    progress_argument IHHty3 HP.
    progress_argument IHHty4 He.
    canonical Hty1 HE h_enumu.
    + exfalso. eapply (bottom_no_value joinability); eassumption.
    + canonical_unfold Hty3 HP. canonical Hty4 He h_enumt; root_progress.
  - progress_argument IHHty2 HD. canonical Hty2 HD h_idesc; root_progress.
  - progress_argument IHHty2 HD. progress_argument IHHty4 Hx.
    canonical Hty2 HD h_idesc; try solve [root_progress].
    all: canonical_unfold Hty4 Hx; root_progress.
  - progress_argument IHHty2 HD. progress_argument IHHty6 Hx.
    canonical Hty2 HD h_idesc; try solve [root_progress].
    all: canonical_unfold Hty6 Hx; root_progress.
  - progress_argument IHHty6 Hx. canonical Hty6 Hx h_muapp; root_progress.
  - progress_argument IHHty7 Hx. canonical Hty7 Hx h_closeapp; root_progress.
  - progress_argument IHHty7 Hx. canonical Hty7 Hx h_closeapp; root_progress.
Qed.
End Progress.

Lemma step_reduction : forall t u, step t u -> reduction t u.
Proof. intros t u H; induction H; eauto using reduction. Qed.

Lemma root_next_step : forall t u, root_step t = Some u -> next_step t = Some u.
Proof. destruct t; intros u H; cbn [next_step]; rewrite H; reflexivity. Qed.

Lemma step_has_next : forall t u, step t u -> exists v, next_step t = Some v.
Proof.
  intros t u H; induction H.
  { eexists; eapply root_next_step; eassumption. }
  all: destruct IHstep as [v Hv]; cbn [next_step];
    destruct (root_step _) eqn:Hr; [eexists; reflexivity|].
  all: repeat match goal with
    | |- context [match next_step ?t with _ => _ end] =>
      destruct (next_step t) eqn:?
    end; try congruence; eexists; reflexivity.
Qed.

Lemma next_step_reduction : forall t u, next_step t = Some u -> reduction t u.
Proof.
  induction t; intros u H; cbn [next_step] in H;
    destruct (root_step _) eqn:Hr;
    try solve [inversion H; subst; now apply red_root].
  all: repeat match type of H with
    | context [match next_step ?t with _ => _ end] =>
        destruct (next_step t) eqn:?
    end; try discriminate; inversion H; subst; eauto using reduction.
Qed.

Lemma accessible_run : forall t, Acc (fun u v => reduction v u) t ->
  exists fuel, next_step (run fuel t) = None.
Proof.
  intros t Hacc; induction Hacc as [t Hnext IH].
  destruct (next_step t) as [u|] eqn:Hu.
  - destruct (IH u (next_step_reduction _ _ Hu)) as [fuel Hfuel].
    exists (S fuel). cbn [run]. now rewrite Hu.
  - exists 0. exact Hu.
Qed.
