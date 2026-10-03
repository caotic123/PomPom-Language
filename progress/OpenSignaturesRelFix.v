(* Index families of relations, relational functors, and impredicative least
   fixed points over families respecting an index relation. These interpret
   inductive data in the binary relational model. *)
From Stdlib Require Import List Arith Bool String Lia.
Require Export OpenSignaturesRelBase.
Import ListNotations.

Definition fam := term -> rel.
Definition functor := fam -> rel.

Definition fam_incl (X Y : fam) := forall i, rel_incl (X i) (Y i).
Definition fam_equiv (X Y : fam) := forall i, rel_equiv (X i) (Y i).
(* Index relation together with conversion of indices. *)
Definition idx (RI : rel) (i i' : term) := RI i i' \/ conv i i'.
Definition fam_resp (RI : rel) (X : fam) :=
  forall i i', closed i -> closed i' -> idx RI i i' -> rel_equiv (X i) (X i').
Definition fam_conv (X : fam) := forall i, closed i -> conv_closed (X i).

(* Functor properties, stated on families respecting the index relation. *)
Definition fmono (RI : rel) (F : functor) := forall X Y,
  fam_resp RI X -> fam_resp RI Y -> fam_incl X Y -> rel_incl (F X) (F Y).
Definition fequiv (RI : rel) (F G : functor) :=
  forall X, fam_resp RI X -> rel_equiv (F X) (G X).
Definition fsym (RI : rel) (F : functor) := forall X Y,
  fam_resp RI X -> fam_resp RI Y ->
  (forall i t u, X i t u -> Y i u t) -> forall t u, F X t u -> F Y u t.
Definition ftrans (RI : rel) (F : functor) := forall X Y Z,
  fam_resp RI X -> fam_resp RI Y -> fam_resp RI Z ->
  fam_conv X -> fam_conv Y -> fam_conv Z ->
  (forall i t u v, X i t u -> Y i u v -> Z i t v) ->
  forall t u v, F X t u -> F Y u v -> F Z t v.
Definition fconv (RI : rel) (F : functor) := forall X, fam_resp RI X -> fam_conv X -> conv_closed (F X).

(* All properties needed of an interpreted description. *)
Definition good_functor (RI : rel) (F : functor) :=
  fmono RI F /\ fsym RI F /\ ftrans RI F /\ fconv RI F.

Lemma fequiv_refl : forall RI F, fequiv RI F F.
Proof. intros RI F X _; apply rel_equiv_refl. Qed.
Lemma fequiv_sym : forall RI F G, fequiv RI F G -> fequiv RI G F.
Proof. intros RI F G H X HX; apply rel_equiv_sym, H, HX. Qed.
Lemma fequiv_trans : forall RI F G H, fequiv RI F G -> fequiv RI G H -> fequiv RI F H.
Proof. intros RI F G H H1 H2 X HX; eapply rel_equiv_trans; [apply H1|apply H2]; exact HX. Qed.

Lemma fmono_equiv : forall RI F X Y, fmono RI F -> fam_resp RI X -> fam_resp RI Y ->
  fam_equiv X Y -> rel_equiv (F X) (F Y).
Proof.
  intros RI F X Y HF HX HY HE t u; split; apply HF; try assumption; intros i a b; apply HE.
Qed.

(* ------------------------------------------------------------------ *)
(* Least fixed points of indexed functors *)

Definition ifunctor := term -> functor.
Definition iresp (RI : rel) (F : ifunctor) :=
  forall j j', closed j -> closed j' -> RI j j -> idx RI j j' -> fequiv RI (F j) (F j').
Definition prefixed (RI : rel) (F : ifunctor) (Y : fam) :=
  forall j t u, closed j -> RI j j -> roll (F j Y) t u -> Y j t u.
Definition mu_rel (RI : rel) (F : ifunctor) : fam := fun i t u =>
  forall Y, fam_resp RI Y -> prefixed RI F Y -> Y i t u.

Section FixedPoints.
Variable RI : rel.
Variable F : ifunctor.
Hypothesis RI_per : per RI.
Hypothesis RI_conv : conv_closed RI.
Hypothesis F_mono : forall j, closed j -> RI j j -> fmono RI (F j).
Hypothesis F_resp : iresp RI F.

Lemma idx_refl_left : forall i i', idx RI i i' -> RI i i -> RI i' i'.
Proof.
  intros i i' [H|H] Hi; [eapply per_refl_right; eassumption|].
  eapply RI_conv; [exact Hi|exact H|exact H].
Qed.
Lemma idx_sym : forall i i', idx RI i i' -> idx RI i' i.
Proof. intros i i' [H|H]; [left; apply (proj1 RI_per); exact H|right; apply cv_sym; exact H]. Qed.

Lemma mu_resp : fam_resp RI (mu_rel RI F).
Proof.
  intros i i' Hc Hc' Hi t u; split; intros H Y HY HP;
    [apply (HY i i' Hc Hc' Hi), H|apply (HY i i' Hc Hc' Hi), H]; assumption.
Qed.

Lemma mu_fold : forall j t u, closed j -> RI j j ->
  roll (F j (mu_rel RI F)) t u -> mu_rel RI F j t u.
Proof.
  intros j t u Hc Hj H Y HY HP; apply HP; [exact Hc|exact Hj|].
  eapply roll_monotone; [|exact H].
  apply F_mono; [exact Hc|exact Hj|apply mu_resp|exact HY|]. intros i a b Hm; exact (Hm Y HY HP).
Qed.

Lemma mu_unfold : forall i t u, closed i -> RI i i ->
  mu_rel RI F i t u -> roll (F i (mu_rel RI F)) t u.
Proof.
  intros i t u Hc Hi H.
  set (Y := fun j a b => closed j /\ RI j j /\ roll (F j (mu_rel RI F)) a b).
  assert (HY : fam_resp RI Y).
  { intros j j' Hcj Hcj' Hj a b; unfold Y; split; intros [_ [Hjj Hr]]; repeat apply conj.
    - exact Hcj'.
    - eapply idx_refl_left; eassumption.
    - apply (roll_equiv _ _ (F_resp j j' Hcj Hcj' Hjj Hj _ mu_resp)), Hr.
    - exact Hcj.
    - eapply idx_refl_left; [apply idx_sym; exact Hj|exact Hjj].
    - apply (roll_equiv _ _ (F_resp j' j Hcj' Hcj Hjj (idx_sym _ _ Hj) _ mu_resp)), Hr. }
  assert (HP : prefixed RI F Y).
  { intros j a b Hcj Hj Hr; repeat apply conj; [exact Hcj|exact Hj|].
    eapply roll_monotone; [|exact Hr].
    apply F_mono; [exact Hcj|exact Hj|exact HY|apply mu_resp|].
    intros k c d [Hck [Hk Hc']]; apply mu_fold; assumption. }
  exact (proj2 (proj2 (H Y HY HP))).
Qed.

Lemma mu_unfold_iff : forall i t u, closed i -> RI i i ->
  (mu_rel RI F i t u <-> roll (F i (mu_rel RI F)) t u).
Proof. intros i t u Hc Hi; split; [apply mu_unfold; assumption|apply mu_fold; assumption]. Qed.

Lemma mu_index : forall i t u, mu_rel RI F i t u -> RI i i.
Proof.
  intros i t u H; apply (H (fun k _ _ => RI k k)).
  - intros k k' _ _ Hk a b; split; intro Hkk;
      [eapply idx_refl_left; eassumption|eapply idx_refl_left; [apply idx_sym; exact Hk|exact Hkk]].
  - intros j a b _ Hj _; exact Hj.
Qed.

Lemma mu_conv : fam_conv (mu_rel RI F).
Proof.
  intros i Hc t t' u u' H Ht Hu; pose proof (mu_index _ _ _ H) as Hi.
  apply mu_fold; [exact Hc|exact Hi|].
  eapply roll_conv; [apply mu_unfold; [exact Hc|exact Hi|exact H]|exact Ht|exact Hu].
Qed.

(* Induction: a respectful family containing the fixed point at the
   subterms of each roll contains the whole fixed point. *)
Lemma mu_induction : forall (P : fam), fam_resp RI P ->
  (forall j t u, closed j -> RI j j ->
    roll (F j (fun k a b => mu_rel RI F k a b /\ P k a b)) t u -> P j t u) ->
  forall i t u, mu_rel RI F i t u -> P i t u.
Proof.
  intros P HPr Hstep i t u H.
  set (Y := fun k a b => mu_rel RI F k a b /\ P k a b).
  assert (HY : fam_resp RI Y).
  { intros k k' Hc Hc' Hk a b; unfold Y; split; intros [Hm Hp]; split;
      try (apply (mu_resp k k' Hc Hc' Hk); exact Hm);
      try (apply (HPr k k' Hc Hc' Hk); exact Hp). }
  assert (HP : prefixed RI F Y).
  { intros j a b Hcj Hj Hr; split.
    - apply mu_fold; [exact Hcj|exact Hj|].
      eapply roll_monotone; [|exact Hr]; apply F_mono; [exact Hcj|exact Hj|exact HY|apply mu_resp|].
      intros k c d [Hc _]; exact Hc.
    - apply Hstep; assumption. }
  exact (proj2 (H Y HY HP)).
Qed.

Hypothesis F_sym : forall j, closed j -> RI j j -> fsym RI (F j).
Hypothesis F_trans : forall j, closed j -> RI j j -> ftrans RI (F j).
Hypothesis F_conv : forall j, closed j -> RI j j -> fconv RI (F j).

Lemma mu_sym : forall i t u, mu_rel RI F i t u -> mu_rel RI F i u t.
Proof.
  intros i t u H.
  set (Y := fun k a b => mu_rel RI F k b a).
  assert (HY : fam_resp RI Y).
  { intros k k' Hc Hc' Hk a b; unfold Y; apply mu_resp; assumption. }
  assert (HP : prefixed RI F Y).
  { intros j a b Hcj Hj [xs [ys [Hx [Hy [Ha [Hb Hr]]]]]]; unfold Y.
    apply mu_fold; [exact Hcj|exact Hj|]. exists ys, xs; repeat apply conj; try assumption.
    eapply F_sym; [exact Hcj|exact Hj|exact HY|apply mu_resp| |exact Hr].
    intros k c d Hm; exact Hm. }
  exact (H Y HY HP).
Qed.

Lemma mu_trans : forall i t u v,
  mu_rel RI F i t u -> mu_rel RI F i u v -> mu_rel RI F i t v.
Proof.
  intros i t u v H.
  set (Y := fun k a b => forall c, mu_rel RI F k b c -> mu_rel RI F k a c).
  assert (HY : fam_resp RI Y).
  { intros k k' Hc Hc' Hk a b; unfold Y; split; intros Hcc c Hb;
      apply (mu_resp k k' Hc Hc' Hk), Hcc, (mu_resp k k' Hc Hc' Hk), Hb. }
  assert (HYc : fam_conv Y).
  { intros k Hck a a' b b' Hab Ha Hb c Hbc. eapply mu_conv; [exact Hck|apply Hab|exact Ha|apply cv_refl].
    eapply mu_conv; [exact Hck|exact Hbc|apply cv_sym; exact Hb|apply cv_refl]. }
  assert (HP : prefixed RI F Y).
  { intros j a b Hcj Hj [xs [ys [Hx [Hy [Ha [Hb Hr]]]]]] c Hbc.
    apply mu_unfold in Hbc; [|exact Hcj|exact Hj].
    destruct Hbc as [ys' [zs [Hy' [Hz [Hb' [Hc Hr']]]]]].
    assert (Hyy : conv ys' ys).
    { apply conv_in_inv; eapply cv_trans; [apply cv_sym; exact Hb'|exact Hb]. }
    apply mu_fold; [exact Hcj|exact Hj|]. exists xs, zs; repeat apply conj; try assumption.
    eapply (F_trans j Hcj Hj Y (mu_rel RI F) (mu_rel RI F));
      [exact HY|apply mu_resp|apply mu_resp|exact HYc|apply mu_conv|apply mu_conv| |exact Hr|].
    - intros k a0 b0 c0 Hab Hbc; exact (Hab c0 Hbc).
    - eapply F_conv; [exact Hcj|exact Hj|apply mu_resp|apply mu_conv|exact Hr'|exact Hyy|apply cv_refl]. }
  intro Huv; exact (H Y HY HP v Huv).
Qed.

Lemma mu_per : forall i, per (mu_rel RI F i).
Proof. intro i; split; [intros t u; apply mu_sym|intros t u v; apply mu_trans]. Qed.

End FixedPoints.

(* Equivalent data give equivalent fixed points. *)
Lemma mu_equiv : forall RI RI' F G,
  rel_equiv RI RI' ->
  (forall j, closed j -> RI j j -> fequiv RI (F j) (G j)) ->
  forall i, rel_equiv (mu_rel RI F i) (mu_rel RI' G i).
Proof.
  intros RI RI' F G HI HF i t u.
  assert (Hresp : forall Y, fam_resp RI Y <-> fam_resp RI' Y).
  { intros Y; split; intros HY k k' Hc Hc' Hk; apply HY; try assumption; destruct Hk as [Hk|Hk];
      [left; apply HI, Hk|right; exact Hk|left; apply HI, Hk|right; exact Hk]. }
  split; intros H Y HY HP.
  - apply H; [apply Hresp, HY|].
    intros j a b Hc Hj Hr; apply HP; [exact Hc|apply HI, Hj|].
    eapply roll_equiv; [|exact Hr]. apply rel_equiv_sym, HF; [exact Hc|exact Hj|apply Hresp, HY].
  - apply H; [apply Hresp, HY|].
    intros j a b Hc Hj Hr; apply HP; [exact Hc|apply HI, Hj|].
    eapply roll_equiv; [|exact Hr]. apply HF; [exact Hc|apply HI, Hj|exact HY].
Qed.
