(* Base vocabulary for the binary relational model used by the coherence
   proofs: conversion-closed relations on closed terms and conversion
   inversion lemmas for canonical constructors. No conjecture is imported. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesObservationalTypes OpenSignaturesRowViews.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Relations *)

Definition rel := term -> term -> Prop.
Definition rel_equiv (R S : rel) := forall t u, R t u <-> S t u.
Definition rel_incl (R S : rel) := forall t u, R t u -> S t u.
Definition rel_sym (R : rel) := forall t u, R t u -> R u t.
Definition rel_trans (R : rel) := forall t u v, R t u -> R u v -> R t v.
Definition per (R : rel) := rel_sym R /\ rel_trans R.
Definition conv_closed (R : rel) :=
  forall t t' u u', R t u -> conv t t' -> conv u u' -> R t' u'.
Definition closed (t : term) := free_vars t = [].

Lemma rel_equiv_refl : forall R, rel_equiv R R.
Proof. intros R t u; tauto. Qed.
Lemma rel_equiv_sym : forall R S, rel_equiv R S -> rel_equiv S R.
Proof. intros R S H t u; specialize (H t u); tauto. Qed.
Lemma rel_equiv_trans : forall R S T, rel_equiv R S -> rel_equiv S T -> rel_equiv R T.
Proof. intros R S T H H' t u; specialize (H t u); specialize (H' t u); tauto. Qed.

Lemma per_refl_left : forall R t u, per R -> R t u -> R t t.
Proof. intros R t u [Hs Ht] H; eapply Ht; [exact H|now apply Hs]. Qed.
Lemma per_refl_right : forall R t u, per R -> R t u -> R u u.
Proof. intros R t u [Hs Ht] H; eapply Ht; [apply Hs; exact H|exact H]. Qed.
Lemma per_equiv : forall R S, rel_equiv R S -> per R -> per S.
Proof.
  intros R S HE [Hs Ht]; split.
  - intros t u H; apply HE, Hs, HE, H.
  - intros t u v H H'; apply HE; eapply Ht; apply HE; eassumption.
Qed.
Lemma conv_closed_equiv : forall R S, rel_equiv R S -> conv_closed R -> conv_closed S.
Proof. intros R S HE HC t t' u u' H Ht Hu; apply HE; eapply HC; [apply HE; exact H|exact Ht|exact Hu]. Qed.

(* ------------------------------------------------------------------ *)
(* Canonical relations *)

Fixpoint code (L : list string) : term :=
  match L with
  | [] => TNilE
  | s :: L => TConsE (TTag s) (code L)
  end.

Definition unit_rel : rel := fun t u => conv t TUnit /\ conv u TUnit.
Definition tag_rel : rel := fun t u => exists s, conv t (TTag s) /\ conv u (TTag s).
Definition code_rel : rel := fun t u => exists L, conv t (code L) /\ conv u (code L).
Definition enum_rel (n : nat) : rel := fun t u =>
  exists m, m < n /\ conv t (enum_position m) /\ conv u (enum_position m).
Definition empty_rel : rel := fun _ _ => False.
Definition pi_rel (RA : rel) (RB : term -> term -> rel) : rel := fun f g =>
  forall a b, closed a -> closed b -> RA a b -> RB a b (TApp f a) (TApp g b).
Definition sigma_rel (RA : rel) (RB : term -> term -> rel) : rel := fun p q =>
  exists a b a' b', closed a /\ closed b /\ closed a' /\ closed b' /\
    conv p (TPair a b) /\ conv q (TPair a' b') /\ RA a a' /\ RB a a' b b'.
Definition roll (R : rel) : rel := fun t u =>
  exists xs ys, closed xs /\ closed ys /\ conv t (TIn xs) /\ conv u (TIn ys) /\ R xs ys.

(* ------------------------------------------------------------------ *)
(* Conversion as an equivalence *)

Lemma conv_app : forall f f' a a', conv f f' -> conv a a' -> conv (TApp f a) (TApp f' a').
Proof. intros; apply cv_compatible, cp_TApp; assumption. Qed.
Lemma conv_app_f : forall f f' a, conv f f' -> conv (TApp f a) (TApp f' a).
Proof. intros; apply conv_app; [assumption|apply cv_refl]. Qed.
Lemma conv_app_a : forall f a a', conv a a' -> conv (TApp f a) (TApp f a').
Proof. intros; apply conv_app; [apply cv_refl|assumption]. Qed.
Lemma conv_pair : forall a a' b b', conv a a' -> conv b b' -> conv (TPair a b) (TPair a' b').
Proof. intros; apply cv_compatible, cp_TPair; assumption. Qed.
Lemma conv_in : forall a a', conv a a' -> conv (TIn a) (TIn a').
Proof. intros; apply cv_compatible, cp_TIn; assumption. Qed.
Lemma conv_fst : forall a a', conv a a' -> conv (TFst a) (TFst a').
Proof. intros; apply cv_compatible, cp_TFst; assumption. Qed.
Lemma conv_snd : forall a a', conv a a' -> conv (TSnd a) (TSnd a').
Proof. intros; apply cv_compatible, cp_TSnd; assumption. Qed.
Lemma conv_root : forall t u, root_step t = Some u -> conv t u.
Proof. intros; now apply cv_step, st_root. Qed.

(* ------------------------------------------------------------------ *)
(* Reduction inversion for canonical constructors *)

Lemma reduces_one : forall t u, reduction t u -> reduces t u.
Proof. intros t u H; eapply reduces_step; [exact H|constructor]. Qed.

Ltac reduction_shape :=
  intros; match goal with H : reduction _ _ |- _ =>
    inversion H; subst; cbn [root_step] in *; try discriminate end;
  repeat eexists; eauto using reduces_one, reduces_refl.

Lemma reduction_pair : forall a b t, reduction (TPair a b) t ->
  exists a' b', t = TPair a' b' /\ reduces a a' /\ reduces b b'.
Proof. reduction_shape. Qed.
Lemma reduction_ipi : forall a b t, reduction (TIPi a b) t ->
  exists a' b', t = TIPi a' b' /\ reduces a a' /\ reduces b b'.
Proof. reduction_shape. Qed.
Lemma reduction_isig : forall a b t, reduction (TISig a b) t ->
  exists a' b', t = TISig a' b' /\ reduces a a' /\ reduces b b'.
Proof. reduction_shape. Qed.
Lemma reduction_mui : forall a b t, reduction (TMuI a b) t ->
  exists a' b', t = TMuI a' b' /\ reduces a a' /\ reduces b b'.
Proof. reduction_shape. Qed.
Lemma reduction_in : forall a t, reduction (TIn a) t -> exists b, t = TIn b /\ reduces a b.
Proof. reduction_shape. Qed.
Lemma reduction_succ : forall a t, reduction (TESucc a) t -> exists b, t = TESucc b /\ reduces a b.
Proof. reduction_shape. Qed.
Lemma reduction_ivar : forall a t, reduction (TIVar a) t -> exists b, t = TIVar b /\ reduces a b.
Proof. reduction_shape. Qed.
Lemma reduction_closeterm : forall a b c t, reduction (TClose a b c) t ->
  exists a' b' c', t = TClose a' b' c' /\ reduces a a' /\ reduces b b' /\ reduces c c'.
Proof. reduction_shape. Qed.
Lemma reduction_sigma : forall x A B u, reduction (TSigma x A B) u ->
  exists A' B', u = TSigma x A' B' /\ reduces A A' /\ reduces B B'.
Proof. reduction_shape. Qed.

Lemma reduces_closeterm : forall a b c t, reduces (TClose a b c) t ->
  exists a' b' c', t = TClose a' b' c' /\ reduces a a' /\ reduces b b' /\ reduces c c'.
Proof.
  intros a b c t H; remember (TClose a b c) as s eqn:E; revert a b c E.
  induction H; intros a b c E; subst.
  - exists a, b, c; repeat split; constructor.
  - destruct (reduction_closeterm _ _ _ _ H) as [a' [b' [c' [-> [Ha [Hb Hc]]]]]].
    destruct (IHreduces _ _ _ eq_refl) as [a'' [b'' [c'' [-> [Ha' [Hb' Hc']]]]]].
    exists a'', b'', c''; repeat split; eauto using reduces_trans.
Qed.
Lemma reduces_sigma : forall x A B u, reduces (TSigma x A B) u ->
  exists A' B', u = TSigma x A' B' /\ reduces A A' /\ reduces B B'.
Proof.
  intros x A B u H; remember (TSigma x A B) as s eqn:E; revert A B E.
  induction H; intros A0 B0 E; subst.
  - exists A0, B0; repeat split; constructor.
  - destruct (reduction_sigma _ _ _ _ H) as [A' [B' [-> [HA HB]]]].
    destruct (IHreduces _ _ eq_refl) as [A'' [B'' [-> [HA' HB']]]].
    exists A'', B''; repeat split; eauto using reduces_trans.
Qed.

(* Applications headed by a closed type family never contract at the root. *)
Lemma reduction_family_app : forall f a t,
  (forall x b, f <> TLam x b) ->
  reduction (TApp f a) t ->
  (exists f', t = TApp f' a /\ reduction f f') \/ (exists a', t = TApp f a' /\ reduction a a').
Proof.
  intros f a t Hf H; inversion H; subst; cbn [root_step] in *.
  - destruct f; try discriminate. exfalso; eapply Hf; reflexivity.
  - left; eauto.
  - right; eauto.
Qed.
Lemma close_not_lam : forall IT F G x b, TClose IT F G <> TLam x b.
Proof. discriminate. Qed.
Lemma mui_not_lam : forall IT D x b, TMuI IT D <> TLam x b.
Proof. discriminate. Qed.
Lemma reduces_closeat : forall IT F G i t, reduces (CloseAt IT F G i) t ->
  exists IT' F' G' i', t = CloseAt IT' F' G' i' /\
    reduces IT IT' /\ reduces F F' /\ reduces G G' /\ reduces i i'.
Proof.
  intros IT F G i t H; remember (CloseAt IT F G i) as s eqn:E; revert IT F G i E.
  induction H; intros IT F G i E; subst.
  - exists IT, F, G, i; repeat split; constructor.
  - unfold CloseAt in H.
    destruct (reduction_family_app _ _ _ (close_not_lam IT F G) H) as [[f' [-> Hf]]|[a' [-> Ha]]].
    + destruct (reduction_closeterm _ _ _ _ Hf) as [a [b [c [-> [Ha [Hb Hc]]]]]].
      destruct (IHreduces a b c i eq_refl) as [a' [b' [c' [i' [-> [Ha' [Hb' [Hc' Hi']]]]]]]].
      exists a', b', c', i'; repeat split; eauto using reduces_trans.
    + destruct (IHreduces IT F G a' eq_refl) as [a'' [b' [c' [i' [-> [Ha' [Hb' [Hc' Hi']]]]]]]].
      exists a'', b', c', i'; repeat split; eauto using reduces_trans, reduces_one.
Qed.
Lemma reduces_muat : forall IT D i t, reduces (MuAt IT D i) t ->
  exists IT' D' i', t = MuAt IT' D' i' /\ reduces IT IT' /\ reduces D D' /\ reduces i i'.
Proof.
  intros IT D i t H; remember (MuAt IT D i) as s eqn:E; revert IT D i E.
  induction H; intros IT D i E; subst.
  - exists IT, D, i; repeat split; constructor.
  - unfold MuAt in H.
    destruct (reduction_family_app _ _ _ (mui_not_lam IT D) H) as [[f' [-> Hf]]|[a' [-> Ha]]].
    + destruct (reduction_mui _ _ _ Hf) as [a [b [-> [Ha Hb]]]].
      destruct (IHreduces a b i eq_refl) as [a' [b' [i' [-> [Ha' [Hb' Hi']]]]]].
      exists a', b', i'; repeat split; eauto using reduces_trans.
    + destruct (IHreduces IT D a' eq_refl) as [a'' [b' [i' [-> [Ha' [Hb' Hi']]]]]].
      exists a'', b', i'; repeat split; eauto using reduces_trans, reduces_one.
Qed.

(* ------------------------------------------------------------------ *)
(* Conversion inversion *)

Ltac alpha_split H :=
  unfold alpha_equiv, alpha_eqb in H; cbn [alpha_eqb_in] in H;
  repeat rewrite Bool.andb_true_iff in H;
  repeat match goal with H0 : _ /\ _ |- _ => destruct H0 end.

Lemma conv_pair_inv : forall a b a' b', conv (TPair a b) (TPair a' b') ->
  conv a a' /\ conv b b'.
Proof.
  intros a b a' b' H; destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_binary TPair reduction_pair _ _ _ Hw) as [x [y [-> [Hx Hy]]]].
  destruct (reduces_binary TPair reduction_pair _ _ _ Hw') as [x' [y' [-> [Hx' Hy']]]].
  alpha_split Ha; split; eapply joined_conv; eassumption.
Qed.
Lemma conv_ipi_inv : forall a b a' b', conv (TIPi a b) (TIPi a' b') -> conv a a' /\ conv b b'.
Proof.
  intros a b a' b' H; destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_binary TIPi reduction_ipi _ _ _ Hw) as [x [y [-> [Hx Hy]]]].
  destruct (reduces_binary TIPi reduction_ipi _ _ _ Hw') as [x' [y' [-> [Hx' Hy']]]].
  alpha_split Ha; split; eapply joined_conv; eassumption.
Qed.
Lemma conv_isig_inv : forall a b a' b', conv (TISig a b) (TISig a' b') -> conv a a' /\ conv b b'.
Proof.
  intros a b a' b' H; destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_binary TISig reduction_isig _ _ _ Hw) as [x [y [-> [Hx Hy]]]].
  destruct (reduces_binary TISig reduction_isig _ _ _ Hw') as [x' [y' [-> [Hx' Hy']]]].
  alpha_split Ha; split; eapply joined_conv; eassumption.
Qed.
Lemma conv_iprod_inv : forall a b a' b', conv (TIProd a b) (TIProd a' b') -> conv a a' /\ conv b b'.
Proof.
  intros a b a' b' H; destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_binary TIProd reduction_iprod _ _ _ Hw) as [x [y [-> [Hx Hy]]]].
  destruct (reduces_binary TIProd reduction_iprod _ _ _ Hw') as [x' [y' [-> [Hx' Hy']]]].
  alpha_split Ha; split; eapply joined_conv; eassumption.
Qed.
Lemma conv_in_inv : forall a b, conv (TIn a) (TIn b) -> conv a b.
Proof.
  apply (conv_unary TIn reduction_in).
  intros a b H; unfold alpha_equiv, alpha_eqb in *; exact H.
Qed.
Lemma conv_succ_inv : forall a b, conv (TESucc a) (TESucc b) -> conv a b.
Proof.
  apply (conv_unary TESucc reduction_succ).
  intros a b H; unfold alpha_equiv, alpha_eqb in *; exact H.
Qed.
Lemma conv_ivar_inv : forall a b, conv (TIVar a) (TIVar b) -> conv a b.
Proof.
  apply (conv_unary TIVar reduction_ivar).
  intros a b H; unfold alpha_equiv, alpha_eqb in *; exact H.
Qed.
Lemma conv_sort_inv : forall j k, conv (TSort j) (TSort k) -> j = k.
Proof.
  intros j k H; destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  apply reduces_sort in Hw; apply reduces_sort in Hw'; subst.
  unfold alpha_equiv, alpha_eqb in Ha; cbn [alpha_eqb_in] in Ha; now apply Nat.eqb_eq.
Qed.
Lemma conv_closeat_inv : forall IT F G i IT' F' G' i',
  conv (CloseAt IT F G i) (CloseAt IT' F' G' i') ->
  conv IT IT' /\ conv F F' /\ conv G G' /\ conv i i'.
Proof.
  intros IT F G i IT' F' G' i' H.
  destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_closeat _ _ _ _ _ Hw) as [a [b [c [d [-> [Ha1 [Hb1 [Hc1 Hd1]]]]]]]].
  destruct (reduces_closeat _ _ _ _ _ Hw') as [a' [b' [c' [d' [-> [Ha2 [Hb2 [Hc2 Hd2]]]]]]]].
  unfold CloseAt in Ha; alpha_split Ha.
  repeat split; eapply joined_conv; eassumption.
Qed.
Lemma conv_muat_inv : forall IT D i IT' D' i',
  conv (MuAt IT D i) (MuAt IT' D' i') -> conv IT IT' /\ conv D D' /\ conv i i'.
Proof.
  intros IT D i IT' D' i' H.
  destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_muat _ _ _ _ Hw) as [a [b [c [-> [Ha1 [Hb1 Hc1]]]]]].
  destruct (reduces_muat _ _ _ _ Hw') as [a' [b' [c' [-> [Ha2 [Hb2 Hc2]]]]]].
  unfold MuAt in Ha; alpha_split Ha.
  repeat split; eapply joined_conv; eassumption.
Qed.

(* Binder inversion: the codomains agree after any closed instantiation. *)
Lemma alpha_binder_subst : forall x y B B' a,
  alpha_eqb_in [x] [y] B B' = true -> closed a ->
  alpha_equiv (subst a x B) (subst a y B').
Proof.
  intros x y B B' a H Ha. unfold alpha_equiv, alpha_eqb, subst.
  eapply alpha_substitute_in; [exact H|].
  intros v w _ _ Hv; cbn [alpha_var] in Hv.
  destruct (v =? x) eqn:Ev, (w =? y) eqn:Ew; try discriminate.
  - apply alpha_eqb_in_refl.
  - cbn [alpha_eqb_in]; exact Hv.
Qed.
Lemma conv_pi_inv : forall x U V y U' V', conv (TPi x U V) (TPi y U' V') ->
  conv U U' /\ forall a, closed a -> conv (subst a x V) (subst a y V').
Proof.
  intros x U V y U' V' H.
  destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_pi _ _ _ _ Hw) as [U1 [V1 [-> [HU HV]]]].
  destruct (reduces_pi _ _ _ _ Hw') as [U2 [V2 [-> [HU' HV']]]].
  unfold alpha_equiv, alpha_eqb in Ha; cbn [alpha_eqb_in] in Ha.
  apply Bool.andb_true_iff in Ha; destruct Ha as [HA HB].
  split; [eapply joined_conv; eassumption|].
  intros a Hclosed.
  eapply cv_trans; [apply conv_subst, reduces_conv; exact HV|].
  eapply cv_trans; [apply cv_alpha, alpha_binder_subst; [exact HB|exact Hclosed]|].
  apply cv_sym, conv_subst, reduces_conv; exact HV'.
Qed.
Lemma conv_sigma_inv : forall x U V y U' V', conv (TSigma x U V) (TSigma y U' V') ->
  conv U U' /\ forall a, closed a -> conv (subst a x V) (subst a y V').
Proof.
  intros x U V y U' V' H.
  destruct (raw_conversion_joinability _ _ H) as [w [w' [Hw [Hw' Ha]]]].
  destruct (reduces_sigma _ _ _ _ Hw) as [U1 [V1 [-> [HU HV]]]].
  destruct (reduces_sigma _ _ _ _ Hw') as [U2 [V2 [-> [HU' HV']]]].
  unfold alpha_equiv, alpha_eqb in Ha; cbn [alpha_eqb_in] in Ha.
  apply Bool.andb_true_iff in Ha; destruct Ha as [HA HB].
  split; [eapply joined_conv; eassumption|].
  intros a Hclosed.
  eapply cv_trans; [apply conv_subst, reduces_conv; exact HV|].
  eapply cv_trans; [apply cv_alpha, alpha_binder_subst; [exact HB|exact Hclosed]|].
  apply cv_sym, conv_subst, reduces_conv; exact HV'.
Qed.

(* Distinct canonical heads never convert. *)
Lemma head_clash : forall t u h k, conv t u ->
  term_head t = Some h -> term_head u = Some k -> h <> k -> False.
Proof. intros t u h k H Ht Hu Hne; apply Hne; eapply raw_head; eassumption. Qed.
Ltac clash H := exfalso; eapply head_clash; [exact H|reflexivity|reflexivity|discriminate].

Lemma conv_position_inv : forall m n, conv (enum_position m) (enum_position n) -> m = n.
Proof.
  induction m as [|m IH]; destruct n as [|n]; cbn [enum_position]; intro H;
    [reflexivity|clash H|clash H|].
  f_equal; apply IH, conv_succ_inv, H.
Qed.
Lemma conv_code_inv : forall L L', conv (code L) (code L') -> L = L'.
Proof.
  induction L as [|s L IH]; destruct L' as [|s' L']; cbn [code]; intro H;
    [reflexivity|clash H|clash H|].
  destruct (conv_conse _ _ _ _ H) as [Hs HL].
  f_equal; [now apply conv_tags|now apply IH].
Qed.

(* ------------------------------------------------------------------ *)
(* Closedness *)

Lemma closed_position : forall n, closed (enum_position n).
Proof. induction n; cbn; [reflexivity|exact IHn]. Qed.
Lemma closed_code : forall L, closed (code L).
Proof. induction L; cbn; [reflexivity|unfold closed in *; cbn; exact IHL]. Qed.
Lemma closed_app : forall f a, closed f -> closed a -> closed (TApp f a).
Proof. unfold closed; intros f a Hf Ha; cbn; rewrite Hf, Ha; reflexivity. Qed.
Lemma closed_app_inv : forall f a, closed (TApp f a) -> closed f /\ closed a.
Proof.
  unfold closed; intros f a H; cbn in H.
  destruct (free_vars f), (free_vars a); cbn in *; try discriminate; auto.
Qed.
Lemma closed_pair : forall a b, closed a -> closed b -> closed (TPair a b).
Proof. unfold closed; intros a b Ha Hb; cbn; rewrite Ha, Hb; reflexivity. Qed.
Lemma closed_in : forall a, closed a -> closed (TIn a).
Proof. unfold closed; intros a Ha; cbn; exact Ha. Qed.

(* ------------------------------------------------------------------ *)
(* The canonical relations are conversion-closed PERs. *)

Lemma unit_rel_per : per unit_rel.
Proof. split; [intros t u [Ht Hu]; split; assumption|intros t u v [Ht _] [_ Hv]; split; assumption]. Qed.
Lemma unit_rel_conv : conv_closed unit_rel.
Proof. intros t t' u u' [Ht Hu] H H'; split; eapply cv_trans; [apply cv_sym; exact H|exact Ht|apply cv_sym; exact H'|exact Hu]. Qed.

Lemma tag_rel_per : per tag_rel.
Proof.
  split; [intros t u [s [Ht Hu]]; exists s; split; assumption|].
  intros t u v [s [Ht Hu]] [s' [Hu' Hv]].
  assert (s = s') by (apply conv_tags; eapply cv_trans; [apply cv_sym; exact Hu|exact Hu']).
  subst; exists s'; split; assumption.
Qed.
Lemma tag_rel_conv : conv_closed tag_rel.
Proof.
  intros t t' u u' [s [Ht Hu]] H H'; exists s; split;
    (eapply cv_trans; [apply cv_sym; eassumption|eassumption]).
Qed.

Lemma code_rel_per : per code_rel.
Proof.
  split; [intros t u [L [Ht Hu]]; exists L; split; assumption|].
  intros t u v [L [Ht Hu]] [L' [Hu' Hv]].
  assert (L = L') by (apply conv_code_inv; eapply cv_trans; [apply cv_sym; exact Hu|exact Hu']).
  subst; exists L'; split; assumption.
Qed.
Lemma code_rel_conv : conv_closed code_rel.
Proof.
  intros t t' u u' [L [Ht Hu]] H H'; exists L; split;
    (eapply cv_trans; [apply cv_sym; eassumption|eassumption]).
Qed.

Lemma enum_rel_per : forall n, per (enum_rel n).
Proof.
  intro n; split; [intros t u [m [Hm [Ht Hu]]]; exists m; repeat split; assumption|].
  intros t u v [m [Hm [Ht Hu]]] [m' [Hm' [Hu' Hv]]].
  assert (m = m') by (apply conv_position_inv; eapply cv_trans; [apply cv_sym; exact Hu|exact Hu']).
  subst; exists m'; repeat split; assumption.
Qed.
Lemma enum_rel_conv : forall n, conv_closed (enum_rel n).
Proof.
  intros n t t' u u' [m [Hm [Ht Hu]]] H H'; exists m; repeat split; [exact Hm| |];
    (eapply cv_trans; [apply cv_sym; eassumption|eassumption]).
Qed.

Lemma empty_rel_per : per empty_rel.
Proof. unfold empty_rel; split; intros t u; [tauto|intros v; tauto]. Qed.
Lemma empty_rel_conv : conv_closed empty_rel.
Proof. unfold conv_closed, empty_rel; tauto. Qed.

Lemma pi_rel_conv : forall RA RB, (forall a b, conv_closed (RB a b)) -> conv_closed (pi_rel RA RB).
Proof.
  intros RA RB HB f f' g g' H Hf Hg a b Ha Hb Hab.
  eapply HB; [apply H; assumption|apply conv_app_f; exact Hf|apply conv_app_f; exact Hg].
Qed.
Lemma sigma_rel_conv : forall RA RB, conv_closed (sigma_rel RA RB).
Proof.
  intros RA RB p p' q q' [a [b [a' [b' [Ha [Hb [Ha' [Hb' [Hp [Hq [HA HB]]]]]]]]]]] H H'.
  exists a, b, a', b'; repeat split; try assumption;
    (eapply cv_trans; [apply cv_sym; eassumption|eassumption]).
Qed.
Lemma roll_conv : forall R, conv_closed (roll R).
Proof.
  intros R t t' u u' [xs [ys [Hx [Hy [Ht [Hu HR]]]]]] H H'.
  exists xs, ys; repeat split; try assumption;
    (eapply cv_trans; [apply cv_sym; eassumption|eassumption]).
Qed.

Lemma roll_per : forall R, per R -> conv_closed R -> per (roll R).
Proof.
  intros R [Hs Ht] HC; split.
  - intros t u [xs [ys [Hx [Hy [Htx [Huy HR]]]]]]; exists ys, xs; repeat split; auto.
  - intros t u v [xs [ys [Hx [Hy [Htx [Huy HR]]]]]] [ys' [zs [Hy' [Hz [Huy' [Hvz HR']]]]]].
    exists xs, zs; repeat split; try assumption.
    eapply Ht; [exact HR|]. eapply HC; [exact HR'| |apply cv_refl].
    apply conv_in_inv; eapply cv_trans; [apply cv_sym; exact Huy'|exact Huy].
Qed.
Lemma roll_monotone : forall R S, rel_incl R S -> rel_incl (roll R) (roll S).
Proof.
  intros R S H t u [xs [ys [Hx [Hy [Ht [Hu HR]]]]]]; exists xs, ys; repeat split; auto.
Qed.
Lemma roll_equiv : forall R S, rel_equiv R S -> rel_equiv (roll R) (roll S).
Proof.
  intros R S H t u; split; apply roll_monotone; intros a b; apply H.
Qed.
