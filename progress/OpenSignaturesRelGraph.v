(* Semantic coercion graphs between closed types. A graph relates related
   closed inhabitants of its source to closed inhabitants of its target.
   Clauses: identity on related types, empty source, contravariant
   functions, retagging enum-tagged sums by name, and rolled close types.
   Function clauses carry closed realizers, so graphs are total. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelViews.
Import ListNotations.

Definition eq_graph (A B : term) : rel := fun a b => closed a /\ closed b /\ rel_at a b A B.
Definition pi_graph (A B : term) (Gd : rel) (Gc : term -> term -> rel) : rel := fun f g =>
  closed f /\ closed g /\ rel_at f f A A /\ rel_at g g B B /\
  forall a' a, Gd a' a -> Gc a' a (TApp f a) (TApp g a').
Definition sum_graph (A B : term) (x : nat) (P : term) (y : nat) (P' : term) (L L' : list string) : rel :=
  fun p q => closed p /\ closed q /\ rel_at p p A A /\ rel_at q q B B /\
    exists m m' s xs ys, nth_error L m = Some s /\ nth_error L' m' = Some s /\ closed xs /\ closed ys /\
      conv p (TPair (enum_position m) xs) /\ conv q (TPair (enum_position m') ys) /\
      rel_at xs ys (subst (enum_position m) x P) (subst (enum_position m') y P').
Definition roll_graph (A B : term) (Gp : rel) : rel := fun t u =>
  closed t /\ closed u /\ rel_at t t A A /\ rel_at u u B B /\
  exists xs ys, closed xs /\ closed ys /\ conv t (TIn xs) /\ conv u (TIn ys) /\ Gp xs ys.

Definition row_live x P y P' (L L' : list string) m :=
  exists m' s, nth_error L m = Some s /\ nth_error L' m' = Some s /\
    rty (subst (enum_position m) x P) (subst (enum_position m') y P').
Definition row_dead x P m :=
  forall t u, closed t -> ~ rel_at t u (subst (enum_position m) x P) (subst (enum_position m) x P).

Inductive Gr : term -> term -> rel -> Prop :=
| gr_eq : forall A B, rty A B -> Gr A B (eq_graph A B)
| gr_empty : forall A B, tyw A -> tyw B -> (forall t u, closed t -> ~ rel_at t u A A) -> Gr A B empty_rel
| gr_pi : forall A B x U V y U' V' Gd Gc c D,
    tyw A -> tyw B -> conv A (TPi x U V) -> conv B (TPi y U' V') ->
    Gr U' U Gd -> closed c ->
    (forall a', closed a' -> rel_at a' a' U' U' -> Gd a' (TApp c a')) ->
    (forall a' a, Gd a' a -> Gr (subst a x V) (subst a' y V') (Gc a' a)) ->
    closed D ->
    (forall a' a t, Gd a' a -> closed t -> rel_at t t (subst a x V) (subst a x V) ->
       Gc a' a t (TApp (TApp D a') t)) ->
    Gr A B (pi_graph A B Gd Gc)
| gr_sum : forall A B x E P y E' P' L L',
    tyw A -> tyw B -> conv A (TSigma x (TEnumT E) P) -> conv E (code L) ->
    conv B (TSigma y (TEnumT E') P') -> conv E' (code L') -> NoDup L' ->
    (forall m, m < List.length L -> row_live x P y P' L L' m \/ row_dead x P m) ->
    Gr A B (sum_graph A B x P y P' L L')
| gr_roll : forall A B IT F G i IT' F' G' i' Gp,
    tyw A -> tyw B -> conv A (CloseAt IT F G i) -> conv B (CloseAt IT' F' G' i') ->
    Gr (payload IT F G i) (payload IT' F' G' i') Gp ->
    Gr A B (roll_graph A B Gp)
| gr_equiv : forall A B G G', Gr A B G -> rel_equiv G G' -> Gr A B G'.

Inductive Gr_shape (A B : term) (G : rel) : Prop :=
| gs_eq : rty A B -> rel_equiv G (eq_graph A B) -> Gr_shape A B G
| gs_empty : tyw A -> tyw B -> (forall t u, closed t -> ~ rel_at t u A A) -> rel_equiv G empty_rel -> Gr_shape A B G
| gs_pi : forall x U V y U' V' Gd Gc c D,
    tyw A -> tyw B -> conv A (TPi x U V) -> conv B (TPi y U' V') ->
    Gr U' U Gd -> closed c ->
    (forall a', closed a' -> rel_at a' a' U' U' -> Gd a' (TApp c a')) ->
    (forall a' a, Gd a' a -> Gr (subst a x V) (subst a' y V') (Gc a' a)) ->
    closed D ->
    (forall a' a t, Gd a' a -> closed t -> rel_at t t (subst a x V) (subst a x V) ->
       Gc a' a t (TApp (TApp D a') t)) ->
    rel_equiv G (pi_graph A B Gd Gc) -> Gr_shape A B G
| gs_sum : forall x E P y E' P' L L',
    tyw A -> tyw B -> conv A (TSigma x (TEnumT E) P) -> conv E (code L) ->
    conv B (TSigma y (TEnumT E') P') -> conv E' (code L') -> NoDup L' ->
    (forall m, m < List.length L -> row_live x P y P' L L' m \/ row_dead x P m) ->
    rel_equiv G (sum_graph A B x P y P' L L') -> Gr_shape A B G
| gs_roll : forall IT F G0 i IT' F' G0' i' Gp,
    tyw A -> tyw B -> conv A (CloseAt IT F G0 i) -> conv B (CloseAt IT' F' G0' i') ->
    Gr (payload IT F G0 i) (payload IT' F' G0' i') Gp ->
    rel_equiv G (roll_graph A B Gp) -> Gr_shape A B G.

Lemma Gr_shape_equiv : forall A B G G', Gr_shape A B G -> rel_equiv G G' -> Gr_shape A B G'.
Proof.
  intros A B G G' H HE; destruct H as [|? ? ? ?|x U V y U' V' Gd Gc c D|? ? ? ? ? ? ? ? ?|];
    [eapply gs_eq|eapply gs_empty|eapply gs_pi with (c := c) (D := D)|eapply gs_sum|eapply gs_roll]; try eassumption;
    (eapply rel_equiv_trans; [apply rel_equiv_sym; exact HE|eassumption]).
Qed.

Lemma Gr_view : forall A B G, Gr A B G -> Gr_shape A B G.
Proof.
  intros A B G H; induction H.
  - eapply gs_eq; eauto using rel_equiv_refl.
  - eapply gs_empty; eauto using rel_equiv_refl.
  - eapply gs_pi with (c := c) (D := D); eauto using rel_equiv_refl.
  - eapply gs_sum; eauto using rel_equiv_refl.
  - eapply gs_roll; eauto using rel_equiv_refl.
  - eapply Gr_shape_equiv; eassumption.
Qed.

Lemma Gr_typed : forall A B G a b, Gr A B G -> G a b ->
  closed a /\ closed b /\ rel_at a a A A /\ rel_at b b B B.
Proof.
  intros A B G a b H Hab; destruct (Gr_view _ _ _ H) as
    [_ HE|_ _ _ HE|? ? ? ? ? ? ? ? ? ? _ _ _ _ _ _ _ _ _ _ HE|? ? ? ? ? ? ? ? _ _ _ _ _ _ _ _ HE
    |? ? ? ? ? ? ? ? ? _ _ _ _ _ HE]; apply HE in Hab.
  - destruct Hab as [Ha [Hb Hr]]; repeat apply conj; try assumption;
      [eapply rel_at_left_of|eapply rel_at_right_of]; exact Hr.
  - destruct Hab.
  - destruct Hab as [Ha [Hb [Hr1 [Hr2 _]]]]; repeat apply conj; assumption.
  - destruct Hab as [Ha [Hb [Hr1 [Hr2 _]]]]; repeat apply conj; assumption.
  - destruct Hab as [Ha [Hb [Hr1 [Hr2 _]]]]; repeat apply conj; assumption.
Qed.

Lemma Gr_tyw : forall A B G, Gr A B G -> tyw A /\ tyw B.
Proof.
  intros A B G H; destruct (Gr_view _ _ _ H); try (split; assumption).
  split; [eapply rty_tyw_l|eapply rty_tyw_r]; eassumption.
Qed.

Lemma nth_error_lt : forall {X} (L : list X) m s, nth_error L m = Some s -> m < List.length L.
Proof. intros X L m s H; apply nth_error_Some; congruence. Qed.

(* Relatedness at a sum or close type follows the tag or the roll. *)
Lemma sum_rel_step : forall A x E P L p p2 m xs, rel_at p p2 A A ->
  conv A (TSigma x (TEnumT E) P) -> conv E (code L) -> conv p (TPair (enum_position m) xs) ->
  exists xs2, closed xs2 /\ conv p2 (TPair (enum_position m) xs2) /\ m < List.length L /\
    rel_at xs xs2 (subst (enum_position m) x P) (subst (enum_position m) x P).
Proof.
  intros A x E P L p p2 m xs H HA HE Hp.
  destruct (sum_rel_iff A A x E P x E P L (rel_at_rty _ _ _ _ (rel_at_left_of _ _ _ _ H)) HA HE HA)
    as [_ [_ Hiff]].
  destruct (proj1 (Hiff p p2) H) as (m2 & xs1 & xs2 & Hm & Hx1 & Hx2 & Hp1 & Hp2 & Hr).
  destruct (conv_pair_inv _ _ _ _ (cv_trans (cv_sym Hp) Hp1)) as [Hpos Hxs].
  apply conv_position_inv in Hpos; subst m2.
  exists xs2; repeat apply conj; try assumption.
  eapply rel_at_conv; [exact Hr|apply cv_sym, Hxs|apply cv_refl|apply cv_refl|apply cv_refl].
Qed.
Lemma close_rel_step : forall A IT F G i t t2 xs, rel_at t t2 A A ->
  conv A (CloseAt IT F G i) -> conv t (TIn xs) ->
  exists xs2, closed xs2 /\ conv t2 (TIn xs2) /\ rel_at xs xs2 (payload IT F G i) (payload IT F G i).
Proof.
  intros A IT F G i t t2 xs H HA Ht.
  destruct (close_rel_iff A A IT F G i IT F G i (rel_at_rty _ _ _ _ (rel_at_left_of _ _ _ _ H)) HA HA)
    as [_ Hiff].
  destruct (proj1 (Hiff t t2) H) as (xs1 & xs2 & Hx1 & Hx2 & Ht1 & Ht2 & Hr).
  pose proof (conv_in_inv _ _ (cv_trans (cv_sym Ht) Ht1)) as Hxs.
  exists xs2; repeat apply conj; try assumption.
  eapply rel_at_conv; [exact Hr|apply cv_sym, Hxs|apply cv_refl|apply cv_refl|apply cv_refl].
Qed.

(* Graphs are closed under relatedness of inputs and outputs. *)
Lemma Gr_closure : forall A B G, Gr A B G -> forall a b a2 b2, G a b -> closed a2 -> closed b2 ->
  rel_at a a2 A A -> rel_at b b2 B B -> G a2 b2.
Proof.
  intros A B G H; induction H; intros a0 b0 a2 b2 Hab Ha2 Hb2 Haa Hbb.
  - destruct Hab as [Ha [Hb Hr]]; refine (conj Ha2 (conj Hb2 _)).
    eapply rel_at_trans; [apply rel_at_sym, Haa|]. eapply rel_at_trans; [exact Hr|exact Hbb].
  - destruct Hab.
  - destruct Hab as [Hf [Hg [Hff [Hgg Hfg]]]].
    refine (conj Ha2 (conj Hb2 (conj (rel_at_right_of _ _ _ _ Haa) (conj (rel_at_right_of _ _ _ _ Hbb) _)))).
    intros a' a Hd. destruct (Gr_typed _ _ _ _ _ H3 Hd) as [Hca' [Hca [Ha'a' Haa']]].
    eapply H7; [exact Hd|exact (Hfg a' a Hd)|apply closed_app; assumption|apply closed_app; assumption| |].
    + eapply pi_app_rel; [exact Haa|exact H1|exact H1|exact Hca|exact Hca|exact Haa'].
    + eapply pi_app_rel; [exact Hbb|exact H2|exact H2|exact Hca'|exact Hca'|exact Ha'a'].
  - destruct Hab as [Hp [Hq [Hpp [Hqq Hx]]]].
    refine (conj Ha2 (conj Hb2 (conj (rel_at_right_of _ _ _ _ Haa) (conj (rel_at_right_of _ _ _ _ Hbb) _)))).
    destruct Hx as (m & m' & s & xs & ys & Hm & Hm' & Hxs & Hys & Hpc & Hqc & Hr).
    destruct (sum_rel_step _ _ _ _ _ _ _ _ _ Haa H1 H2 Hpc) as (xs2 & Hxs2 & Hp2 & _ & Hr1).
    destruct (sum_rel_step _ _ _ _ _ _ _ _ _ Hbb H3 H4 Hqc) as (ys2 & Hys2 & Hq2 & _ & Hr2).
    exists m, m', s, xs2, ys2; repeat apply conj; try assumption.
    eapply rel_at_trans; [apply rel_at_sym, Hr1|]. eapply rel_at_trans; [exact Hr|exact Hr2].
  - destruct Hab as [Ht [Hu [Htt [Huu Hx]]]].
    refine (conj Ha2 (conj Hb2 (conj (rel_at_right_of _ _ _ _ Haa) (conj (rel_at_right_of _ _ _ _ Hbb) _)))).
    destruct Hx as (xs & ys & Hxs & Hys & Htc & Huc & Hp).
    destruct (close_rel_step _ _ _ _ _ _ _ _ Haa H1 Htc) as (xs2 & Hxs2 & Ht2 & Hr1).
    destruct (close_rel_step _ _ _ _ _ _ _ _ Hbb H2 Huc) as (ys2 & Hys2 & Hu2 & Hr2).
    exists xs2, ys2; repeat apply conj; try assumption.
    eapply IHGr; eassumption.
  - apply H0; eapply IHGr; [apply H0, Hab|eassumption..].
Qed.

Lemma rty_of_rel_self : forall a A A2, rel_at a a A A -> rty A A2 -> rel_at a a A A2.
Proof. intros; apply rel_at_rty_both; assumption. Qed.

(* Graphs only depend on their types up to relatedness. *)
Lemma Gr_transport : forall A B G, Gr A B G -> forall A2 B2, rty A A2 -> rty B B2 -> Gr A2 B2 G.
Proof.
  intros A B G H; induction H; intros A2 B2 HA2 HB2.
  - eapply gr_equiv; [apply gr_eq; eapply rty_trans; [apply rty_sym, HA2|eapply rty_trans; [exact H|exact HB2]]|].
    intros a b; split; intros [Ha [Hb Hr]]; refine (conj Ha (conj Hb _)); eapply rel_at_retype; try eassumption;
      apply rty_sym; assumption.
  - apply gr_empty; [eapply rty_tyw_r; exact HA2|eapply rty_tyw_r; exact HB2|].
    intros t u Hc Ht; apply (H1 t u Hc). eapply rel_at_retype; [exact Ht|apply rty_sym, HA2|apply rty_sym, HA2].
  - rename H7 into IHc.
    destruct (pi_ex _ _ _ _ _ HA2 H1) as [x2 [U2 [V2 HA2c]]].
    destruct (pi_ex _ _ _ _ _ HB2 H2) as [y2 [U2' [V2' HB2c]]].
    destruct (pi_rty _ _ _ _ _ _ _ _ HA2 H1 HA2c) as [HU HV].
    destruct (pi_rty _ _ _ _ _ _ _ _ HB2 H2 HB2c) as [HU' HV'].
    eapply gr_equiv; [eapply gr_pi with (x := x2) (U := U2) (V := V2) (y := y2) (U' := U2') (V' := V2') (c := c) (D := D)|].
    + eapply rty_tyw_r; exact HA2.
    + eapply rty_tyw_r; exact HB2.
    + exact HA2c.
    + exact HB2c.
    + apply IHGr; assumption.
    + exact H4.
    + intros a' Ha' Hr. apply H5; [exact Ha'|]. eapply rel_at_retype; [exact Hr|apply rty_sym, HU'|apply rty_sym, HU'].
    + intros a' a Hd. destruct (Gr_typed _ _ _ _ _ H3 Hd) as [Hca' [Hca [Ha'a' Haa]]].
      apply IHc; [exact Hd|apply HV; [exact Hca|exact Hca|apply rel_at_rty_both; assumption]
        |apply HV'; [exact Hca'|exact Hca'|apply rel_at_rty_both; assumption]].
    + exact H8.
    + intros a' a t Hd Ht Htt. destruct (Gr_typed _ _ _ _ _ H3 Hd) as [Hca' [Hca [Ha'a' Haa]]].
      apply H9; [exact Hd|exact Ht|]. eapply rel_at_retype; [exact Htt| |];
        apply rty_sym, HV; [exact Hca|exact Hca|apply rel_at_rty_both; assumption|exact Hca|exact Hca|apply rel_at_rty_both; assumption].
    + intros f g; split; intros [Hf [Hg [Hff [Hgg Hx]]]]; refine (conj Hf (conj Hg (conj _ (conj _ Hx))));
        eapply rel_at_retype; try eassumption; apply rty_sym; assumption.
  - destruct (sum_ex _ _ _ _ _ _ HA2 H1 H2) as [x2 [E2 [P2 HA2c]]].
    destruct (sum_ex _ _ _ _ _ _ HB2 H3 H4) as [y2 [E2' [P2' HB2c]]].
    destruct (sum_rel_iff _ _ _ _ _ _ _ _ _ HA2 H1 H2 HA2c) as [HE2 [HP2 _]].
    destruct (sum_rel_iff _ _ _ _ _ _ _ _ _ HB2 H3 H4 HB2c) as [HE2' [HP2' _]].
    eapply gr_equiv; [eapply gr_sum with (x := x2) (E := E2) (P := P2) (y := y2) (E' := E2') (P' := P2') (L := L) (L' := L')|].
    + eapply rty_tyw_r; exact HA2.
    + eapply rty_tyw_r; exact HB2.
    + exact HA2c.
    + exact HE2.
    + exact HB2c.
    + exact HE2'.
    + exact H5.
    + intros m Hm; destruct (H6 m Hm) as [(m' & s & Hs & Hs' & Hr)|Hd]; [left|right].
      * exists m', s; repeat apply conj; try assumption.
        eapply rty_trans; [apply rty_sym, HP2, Hm|]. eapply rty_trans; [exact Hr|apply HP2', (nth_error_lt _ _ _ Hs')].
      * intros t u Hc Ht; apply (Hd t u Hc). eapply rel_at_retype; [exact Ht|apply rty_sym, HP2, Hm|apply rty_sym, HP2, Hm].
    + intros p q; split; intros [Hp [Hq [Hpp [Hqq Hx]]]];
        (refine (conj Hp (conj Hq (conj _ (conj _ _)))); [eapply rel_at_retype; try eassumption; try (apply rty_sym; assumption)
         |eapply rel_at_retype; try eassumption; try (apply rty_sym; assumption)|]);
        destruct Hx as (m & m' & s & xs & ys & Hm & Hm' & Hxs & Hys & Hpc & Hqc & Hr);
        exists m, m', s, xs, ys; repeat apply conj; try assumption; eapply rel_at_retype; try exact Hr.
      all: first [apply HP2, (nth_error_lt _ _ _ Hm) | apply HP2', (nth_error_lt _ _ _ Hm')
        | apply rty_sym, HP2, (nth_error_lt _ _ _ Hm) | apply rty_sym, HP2', (nth_error_lt _ _ _ Hm')].
  - destruct (close_ex _ _ _ _ _ _ HA2 H1) as (IT2 & F2 & G2 & i2 & HA2c).
    destruct (close_ex _ _ _ _ _ _ HB2 H2) as (IT2' & F2' & G2' & i2' & HB2c).
    destruct (close_rel_iff _ _ _ _ _ _ _ _ _ _ HA2 H1 HA2c) as [HP _].
    destruct (close_rel_iff _ _ _ _ _ _ _ _ _ _ HB2 H2 HB2c) as [HP' _].
    eapply gr_equiv; [eapply gr_roll with (IT := IT2) (F := F2) (G := G2) (i := i2) (IT' := IT2') (F' := F2') (G' := G2') (i' := i2')|].
    + eapply rty_tyw_r; exact HA2.
    + eapply rty_tyw_r; exact HB2.
    + exact HA2c.
    + exact HB2c.
    + apply IHGr; assumption.
    + intros t u; split; intros [Ht [Hu [Htt [Huu Hx]]]]; refine (conj Ht (conj Hu (conj _ (conj _ Hx))));
        eapply rel_at_retype; try eassumption; apply rty_sym; assumption.
  - eapply gr_equiv; [apply IHGr; assumption|exact H0].
Qed.

Lemma Gr_transport_l : forall A B G A2, Gr A B G -> rty A A2 -> Gr A2 B G.
Proof. intros; eapply Gr_transport; [eassumption|eassumption|apply tyw_rty, (proj2 (Gr_tyw _ _ _ H))]. Qed.
Lemma Gr_transport_r : forall A B G B2, Gr A B G -> rty B B2 -> Gr A B2 G.
Proof. intros; eapply Gr_transport; [eassumption|apply tyw_rty, (proj1 (Gr_tyw _ _ _ H))|eassumption]. Qed.
